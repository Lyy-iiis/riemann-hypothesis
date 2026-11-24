module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHTFormOver
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GenWeil
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.MemEigSpOfMemHtDual
public import Mathlib.Tactic.ENatToNat
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsCptGen
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsStalkFractionOfGeneric
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LieModel
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsUniqueTangentDualNumber
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SectionEqZeroOfValues
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SectionExtendsFromStalkPullback
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionLiftIsClosedImmersion
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorusPointOverFractionField
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.HtExists
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsOfPolAV
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
public import Development.AbelianVarietyTheory.Counterexamples.AbelianLawCounterexamples.ExistsTwoTorsionWeilDegenerate
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjIsAbelianSchemeDimRigidifiedSym
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsGenericWeilPairing
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsTorsionQuasiFiniteGroup
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.WeilPairingPullbackIff
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsWithoutCohomology
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Linter.HaveILetI
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FullTorsionIntegrallyClosedStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaObjOfDescendedData
import Development.AbelianVarietyTheory.Statements.HyperbolicHypotheses.HypothesesInhabitedHyperbolic

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.WeilBound.CoreStatements.HomogeneousNonvanishing.LatticeIntegrallyClosedTorsion

-- ===== clump member: Development.WeilBound.CoreStatements.HomogeneousNonvanishing.LatticeIntegrallyClosedTorsion =====
section -- clump:auto
@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.OmLinkK

theorem htOm_eq_htLat : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B : Type) [CommRing B] (b : Base l B) (X : Scheme.{0}) (Ω : Type) [Field Ω] [CharZero Ω] (ξ : Sp Ω ⟶ X) (s : Sp Ω ⟶ Sp B) (o : Obj D l b s) (t : SAB H X) (_ : SABMap o.t t ξ) (V : Type) [AddCommGroup V] [Module Ω V] (M : LieModel t.G ξ V) (n : ℕ) (q : Cpt ξ), IsCptGen ξ → 0 < n → FullTorsion t.G ξ n → IsIntegrallyClosed (X.presheaf.stalk q.1) → IsNoetherianRing (X.presheaf.stalk q.1) → M.IsHTFormAt n q 0 ∧ (0 < D.p + D.q → ∃ ζ : Ω, IsPrimitiveRoot ζ n) ∧ M.htOm t.PP.L n q = M.htLat n q :=
  _root_.GlobalTheory.T.full_torsion_integrally_closed

end GlobalTheory.CompanionTheory.Ar.OmLinkK

namespace PositivityTheory.UnitarySelfGeneration

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

theorem lattice_integrally_closed_torsion : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B : Type) [CommRing B] (b : Base l B) (X : Scheme.{0}) (Ω : Type) [Field Ω] [CharZero Ω] (ξ : Sp Ω ⟶ X) (s : Sp Ω ⟶ Sp B) (o : Obj D l b s) (t : SAB H X) (_ : SABMap o.t t ξ) (V : Type) [AddCommGroup V] [Module Ω V] (M : LieModel t.G ξ V) (n : ℕ) (q : Cpt ξ), IsCptGen ξ → 0 < n → FullTorsion t.G ξ n → IsIntegrallyClosed (X.presheaf.stalk q.1) → IsNoetherianRing (X.presheaf.stalk q.1) → M.IsHTFormAt n q 0 ∧ (0 < D.p + D.q → ∃ ζ : Ω, IsPrimitiveRoot ζ n) ∧ M.htOm t.PP.L n q = M.htLat n q :=
  @GlobalTheory.CompanionTheory.Ar.OmLinkK.htOm_eq_htLat

end PositivityTheory.UnitarySelfGeneration
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.WeilBound.CoreStatements.HomogeneousNonvanishing.LatticeIntegrallyClosedTorsion =====
