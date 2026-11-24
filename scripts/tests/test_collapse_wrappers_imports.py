"""Check import modifiers when a caller of a wrapper would have its header rewritten."""
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest


SCRIPT = Path(__file__).resolve().parents[1] / "collapse_wrappers.py"


class CallerImports(unittest.TestCase):
    def test_keep_import_modifiers_in_callers(self):
        for modifier in ("import all", "public meta import"):
            with self.subTest(modifier=modifier), tempfile.TemporaryDirectory() as directory:
                src = Path(directory) / "src"
                src.mkdir()
                (src / "Core.lean").write_text(
                    "module\n@[expose] public section\n"
                    "theorem original : True := by trivial\n"
                    "theorem other : True := by trivial\n")
                (src / "Alias.lean").write_text(
                    "module\npublic import Core\n@[expose] public section\n"
                    "theorem aliasProof : True := original\n")
                (src / "Impl.lean").write_text("module\npublic def answer : Nat := 42\n")
                caller = src / "User.lean"
                use = ("example : answer = 42 := rfl" if modifier == "import all" else
                       "meta def useAnswer : Nat := answer\nexample : True := aliasProof")
                caller.write_text(f"module\nimport Alias\n{modifier} Impl\n{use}\n")

                subprocess.run(["git", "init", "-q", directory], check=True)
                subprocess.run(["git", "-C", directory, "add", "src"], check=True)
                subprocess.run([sys.executable, str(SCRIPT), directory], check=True)
                self.assertIn(f"\n{modifier} Impl\n", caller.read_text())
                if lean := os.environ.get("LEAN"):
                    for name in ("Core", "Alias", "Impl", "User"):
                        if (src / f"{name}.lean").exists():
                            subprocess.run([lean, "-o", f"{name}.olean", f"{name}.lean"], cwd=src,
                                           env={**os.environ, "LEAN_PATH": str(src)}, check=True)


if __name__ == "__main__":
    unittest.main()
