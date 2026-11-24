module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PoincareDeRhamDuality
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CubeTheorem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeDeRhamStructureOfCubeDualPoincare
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.CubeTheorem.CubeTheoremHolds
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeDeRhamLocallyFreeHodgeDegeneratesStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualAbelianSchemeExistsBidualityStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PoincareDeRhamDualityOfHodgeDeRhamDual
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianDeRhamOfHodgeDualPoincare, Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeFirstDeRhamStructure

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianDeRhamOfHodgeDualPoincare =====
section -- clump:auto
@[expose] public section

namespace GlobalTheory

theorem abelianDeRham_of_hodge_dual_poincare :
    GlobalTheory.Published.AbelianHodgeDeRham → GlobalTheory.Published.DualAbelianScheme →
      GlobalTheory.Published.PoincareDeRhamDuality → GlobalTheory.Published.AbelianDeRham :=
  fun h₁ h₂ h₃ => _root_.GlobalTheory.abelianDeRham_of_hodge_cube_dual_poincare h₁ _root_.GlobalTheory.SpreadingModels.cubeTheorem_holds h₂ h₃

end GlobalTheory
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianDeRhamOfHodgeDualPoincare =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeFirstDeRhamStructure =====
section -- clump:auto
@[expose] public section

namespace GlobalTheory

theorem abelianDeRham : GlobalTheory.Published.AbelianDeRham :=
  GlobalTheory.abelianDeRham_of_hodge_dual_poincare GlobalTheory.T.abelianScheme_deRham_locallyFree_hodgeDegenerates GlobalTheory.T.dualAbelianScheme_exists_biduality
    (GlobalTheory.PoincareDeRhamDualityProof.poincareDeRhamDuality_of_hodge GlobalTheory.T.abelianScheme_deRham_locallyFree_hodgeDegenerates GlobalTheory.T.dualAbelianScheme_exists_biduality)

end GlobalTheory
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeFirstDeRhamStructure =====
