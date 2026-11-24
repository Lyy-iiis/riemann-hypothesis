module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsNoetherianRingDualNumber
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeSquareZeroLiftsOfHodgeDeRham
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineSmoothLiftOfRelations
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PoincareDeRhamDuality
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CubeTheorem
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianLifting
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianUnobstructed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianLiftingOfDeRhamUnobstructed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeDeRhamStructureOfCubeDualPoincare
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.CubeTheorem.CubeTheoremHolds
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeDeRhamLocallyFreeHodgeDegeneratesStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeUnobstructedSquareZeroAffine
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
-- Members: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeSquareZeroLiftsOfDeRhamCohomology, Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeSquareZeroLiftsOfDeRhamCohomologyStatement, Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeHomLiftingNilDPOfFiveStatements, Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianLiftingOfFour, Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeHomLiftingNilpotentDividedPowers

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeSquareZeroLiftsOfDeRhamCohomology =====
section -- clump:auto
@[expose] public section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LiftSys

theorem abelianSchemeLifts_of_abelianHodgeDeRham : AbelianHodgeDeRham → AbelianSchemeLifts :=
  abelianSchemeLifts_of_hodgeDeRham
    GlobalTheory.SmoothLift.crystallineSmoothLift_of_relations

end GlobalTheory.LiftSys
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeSquareZeroLiftsOfDeRhamCohomology =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeSquareZeroLiftsOfDeRhamCohomologyStatement =====
section -- clump:auto
@[expose] public section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.abelianSchemeSquareZeroLifts_of_deRhamCohomology : AbelianHodgeDeRham → AbelianSchemeLifts := by
  first | exact @GlobalTheory.LiftSys.abelianSchemeLifts_of_abelianHodgeDeRham
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeSquareZeroLiftsOfDeRhamCohomologyStatement =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeHomLiftingNilDPOfFiveStatements =====
section -- clump:auto
@[expose] public section

theorem GlobalTheory.SqLift.abelianLifting_of_known_theorems :
    GlobalTheory.Published.AbelianHodgeDeRham → GlobalTheory.Published.CubeTheorem → GlobalTheory.Published.DualAbelianScheme →
      GlobalTheory.Published.PoincareDeRhamDuality → GlobalTheory.Published.AbelianUnobstructed →
      GlobalTheory.Published.AbelianLifting :=
  fun a b c d e =>
    GlobalTheory.SqLift.abelianLifting_of_schemeLifts (_root_.GlobalTheory.abelianDeRham_of_hodge_cube_dual_poincare a b c d) (GlobalTheory.T.abelianSchemeSquareZeroLifts_of_deRhamCohomology a) e
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeHomLiftingNilDPOfFiveStatements =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianLiftingOfFour =====
section -- clump:auto
@[expose] public section

namespace GlobalTheory.LiftFour

theorem abelianLifting_of_four :
    GlobalTheory.Published.AbelianHodgeDeRham → GlobalTheory.Published.DualAbelianScheme →
      GlobalTheory.Published.PoincareDeRhamDuality → GlobalTheory.Published.AbelianUnobstructed →
      GlobalTheory.Published.AbelianLifting :=
  fun a c d e => _root_.GlobalTheory.SqLift.abelianLifting_of_known_theorems a _root_.GlobalTheory.SpreadingModels.cubeTheorem_holds c d e

end GlobalTheory.LiftFour
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianLiftingOfFour =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeHomLiftingNilpotentDividedPowers =====
section -- clump:auto
@[expose] public section

namespace GlobalTheory

theorem abelianScheme_hom_lifting_nilpotent_dividedPowers : GlobalTheory.Published.AbelianLifting :=
  GlobalTheory.LiftFour.abelianLifting_of_four GlobalTheory.T.abelianScheme_deRham_locallyFree_hodgeDegenerates GlobalTheory.T.dualAbelianScheme_exists_biduality
    (GlobalTheory.PoincareDeRhamDualityProof.poincareDeRhamDuality_of_hodge GlobalTheory.T.abelianScheme_deRham_locallyFree_hodgeDegenerates GlobalTheory.T.dualAbelianScheme_exists_biduality)
    GlobalTheory.UnobTop.abelianUnobstructed

end GlobalTheory
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeHomLiftingNilpotentDividedPowers =====
