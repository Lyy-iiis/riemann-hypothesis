module

public import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
public import Formalism.LocalToGlobal.Columns.AbelianHostFieldConditions
public import Formalism.PeriodIntegrals.AlgValsFin
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AlgebraicValuesFinite.AlgValsFinMain
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipA

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Formalism.LocalToGlobal.UnitaryNorms.CharExCol, Formalism.PeriodIntegrals.OrbitalBoundsConclusion.AlgValsFin, Formalism.LocalToGlobal.UnitaryNorms.CharExVal

-- ===== clump member: Formalism.LocalToGlobal.UnitaryNorms.CharExCol =====
section -- clump:auto
@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR

namespace Formalism.L2.Host

namespace CharEx

def AlgValsFin (L : Type) [Field L] [NumberField L] : Prop :=
  ∀ (χ : HChar L) (s : ℝ) (m : (L →+* ℂ) → ℤ),
    (∀ k : Lˣ, ((χ.inf k : ℂˣ) : ℂ) * ∏ φ : L →+* ℂ, ((‖φ (k : L)‖ : ℝ) : ℂ) ^ (s : ℂ) = ∏ φ : L →+* ℂ, φ (k : L) ^ m φ) →
    ∃ C : Subfield ℂ, FiniteDimensional ℚ C ∧ χ.ValuesIn s C.subtype

open Formalism.L2.Col

variable {X : Fields} (σ₀ : X.K →+* ℂ)


end CharEx

end Formalism.L2.Host
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.LocalToGlobal.UnitaryNorms.CharExCol =====

-- ===== clump member: Formalism.PeriodIntegrals.OrbitalBoundsConclusion.AlgValsFin =====
section -- clump:auto
@[expose] public section

theorem algValsFin (L : Type) [Field L] [NumberField L] : PI.AlgValsFin.AlgValsFin L :=
  _root_.PI.AlgValsFin.W.algValsFin_main L
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.PeriodIntegrals.OrbitalBoundsConclusion.AlgValsFin =====

-- ===== clump member: Formalism.LocalToGlobal.UnitaryNorms.CharExVal =====
section -- clump:auto
@[expose] public section

namespace Formalism.L2.Host

namespace CharEx

theorem algValsFin (L : Type) [Field L] [NumberField L] : AlgValsFin L := _root_.PI.AlgValsFin.W.algValsFin_main L

end CharEx

end Formalism.L2.Host
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.LocalToGlobal.UnitaryNorms.CharExVal =====
