module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.TwistingSheafOneChartEqPreimageStandardChart
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRegularCoverOfAlteration, Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProjOverOfIsFiniteOverProjective

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRegularCoverOfAlteration =====
section -- clump:auto
@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.RegCoverExists

set_option autoImplicit false in
open CategoryTheory AlgebraicGeometry in
private theorem isSeparated_spMap {R R' : Type} [CommRing R] [CommRing R'] (c : R →+* R') :
    IsSeparated (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap c) := by
  have : IsAffine (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R) := by
    show IsAffine (Spec (CommRingCat.of R)); infer_instance
  have : IsAffine (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R') := by
    show IsAffine (Spec (CommRingCat.of R')); infer_instance
  infer_instance


set_option autoImplicit false in
open CategoryTheory AlgebraicGeometry in
theorem _root_.GlobalTheory.RegCoverExists.isProjOver_of_comp_spMap {R R' : Type} [CommRing R] [CommRing R'] (c : R →+* R')
    {Y : Scheme.{0}} {f : Y ⟶ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R'} (h : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsProjOver (f ≫ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap c)) : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsProjOver f := by
  obtain ⟨N, i, hi, hif⟩ := h
  have hP := _root_.GlobalTheory.ProjSpace.isPullback_baseChange N c
  haveI := isSeparated_spMap c
  haveI : IsSeparated (_root_.GlobalTheory.ProjSpace.baseChange N c) :=
    MorphismProperty.of_isPullback (P := @IsSeparated) hP.flip inferInstance
  refine ⟨N, hP.lift i f hif, ?_, hP.lift_snd _ _ _⟩
  haveI : IsClosedImmersion (hP.lift i f hif ≫ _root_.GlobalTheory.ProjSpace.baseChange N c) := by
    rw [hP.lift_fst]; exact hi
  exact IsClosedImmersion.of_comp _ (_root_.GlobalTheory.ProjSpace.baseChange N c)

end GlobalTheory.RegCoverExists

end
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRegularCoverOfAlteration =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProjOverOfIsFiniteOverProjective =====
section -- clump:auto
@[expose] public section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc

namespace GlobalTheory.FiniteOverProj

theorem isProjOver_of_isFinite_over :
    ∀ (A o : Type) [CommRing A] [CommRing o] (κ : A →+* o) (M Z : Scheme.{0}) (z : Z ⟶ Sp A) (π : M ⟶ Z) (s : M ⟶ Sp o), IsProjOver z → IsFinite π → IsNoetherianRing A → s ≫ spMap κ = π ≫ z → IsProjOver s := by
  intro A o _ _ κ M Z z π s hz hπ _ hs
  have h : IsProjOver (π ≫ z) := GlobalTheory.isProjOver_comp_of_isFinite π hz
  rw [← hs] at h
  exact GlobalTheory.RegCoverExists.isProjOver_of_comp_spMap κ h

end GlobalTheory.FiniteOverProj

end
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProjOverOfIsFiniteOverProjective =====
