module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.Precomp
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.TwistingSheafOneChartEqPreimageStandardChart
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.InclStd
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConeCocycleClassIndependent
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConeCocycleClosed
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsConeLift
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
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.IsTautologicalLineAt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConeLiftRatioMemIdeal
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Tactic.Polynomial.Basic
import Std.Tactic.BVDecide.Normalize.Prop

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SupremumTwistingOpensEqTop, Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.RSubOneMem

-- ===== clump member: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SupremumTwistingOpensEqTop =====
section -- clump:auto
@[expose] public section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.ConeCover

attribute [local instance] MvPolynomial.gradedAlgebra

theorem main : ∀ {R : Type} [CommRing R] {X : Scheme.{0}} (D : E.LineData X) (N : ℕ)
    (i : X ⟶ ReciprocityTheory.ChartRestriction.G.Geo.Tor.PSpace R N), IsTautologicalLineAt D N i → sSup (𝒱D D) = ⊤ := by
  intro R _ X D N i h
  obtain ⟨-, s, hs, -⟩ := h
  rw [eq_top_iff]
  intro x _
  obtain ⟨j, hj⟩ := GlobalTheory.ProjSpace.exists_mem_chart R N (i x)
  haveI : IsOpenImmersion (chart R N j) := by
    unfold chart
    infer_instance
  have hmem : (pullback.fst i (chart R N j)).opensRange ∈ 𝒱D D :=
    ⟨(pullback.fst i (chart R N j)).isoOpensRange.inv ≫ s j, by
      rw [Category.assoc, hs, Scheme.Hom.isoOpensRange_inv_comp]⟩
  refine TopologicalSpace.Opens.mem_sSup.2 ⟨_, hmem, ?_⟩
  have e : (chart R N j).opensRange = GlobalTheory.ProjSpace.chart R N j := Proj.opensRange_awayι _ _ _ _
  have hr : i x ∈ ((chart R N j).opensRange : Set _) := by
    rw [e]
    exact hj
  rw [Scheme.Hom.coe_opensRange] at hr
  show x ∈ ((pullback.fst i (chart R N j)).opensRange : Set X)
  rw [Scheme.Hom.coe_opensRange, Scheme.Pullback.range_fst]
  exact hr

end GlobalTheory.CompanionTheory.ConeCover
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SupremumTwistingOpensEqTop =====

-- ===== clump member: Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.RSubOneMem =====
section -- clump:auto
@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris DividedPowers

namespace CrystallineSemistableComparison.Pb

theorem dpow_mem_pdP {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) (n : ℕ) {x : B} (hx : x ∈ J) :
    δ.dpow n x ∈ pdP δ n :=
  Ideal.subset_span ⟨[(n, x)], by simpa using hx, by simp, by simp⟩

theorem dividedPowerFiltration_anti {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) {r r' : ℕ} (h : r ≤ r') :
    pdP δ r' ≤ pdP δ r :=
  Ideal.span_le.2 fun _ ⟨l, hl, hr, hz⟩ => Ideal.subset_span ⟨l, hl, h.trans hr, hz⟩

theorem plogK_congr {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) {s s' : ℕ} (h : s ≤ s')
    (hs : pdP δ s = ⊥) {x : B} (hx : x ∈ J) : plogK δ s x = plogK δ s' x := by
  unfold plogK
  refine Finset.sum_subset (Finset.range_mono h) fun k _ hk => ?_
  have hk' : s ≤ k + 1 := by simp at hk; omega
  have hm : δ.dpow (k + 1) x ∈ pdP δ s := dividedPowerFiltration_anti δ hk' (dpow_mem_pdP δ _ hx)
  rw [hs, Ideal.mem_bot] at hm
  rw [hm, mul_zero]

theorem plogK_mem {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) (s : ℕ) {x : B} (hx : x ∈ J) :
    plogK δ s x ∈ J :=
  Ideal.sum_mem _ fun k _ => Ideal.mul_mem_left _ _ (δ.dpow_mem (Nat.succ_ne_zero k) hx)

section K
variable {K : Type} [Field K] [CharZero K] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of K)}

theorem r_sub_one_mem {C : Type 1} [Category.{0} C] {g : C ⥤ Thick (smFun X q)} {D : E.LineData X} (Λ : CLiftK g D)
    (σ : ComposableArrows C 2) : ((Λ.r σ : (g.obj (σ.obj (Fin.last 2))).B) - 1) ∈ (g.obj (σ.obj (Fin.last 2))).J := _root_.GlobalTheory.CompanionTheory.ConeUnit.r_sub_one Λ σ

theorem zK_cocycle {C : Type 1} [Category.{0} C] {g : C ⥤ Thick (smFun X q)} {D : E.LineData X} (Λ : CLiftK g D)
    (s : ℕ) (hs : ∀ c, (g.obj c).pdPow s = ⊥) : CH.d _ 2 (zK Λ s) = 0 := _root_.GlobalTheory.CompanionTheory.ConeZcoc.main Λ s hs

theorem zK_cls_eq {C : Type 1} [Category.{0} C] {g : C ⥤ Thick (smFun X q)} {D : E.LineData X} (Λ Λ' : CLiftK g D)
    (s : ℕ) (hs : ∀ c, (g.obj c).pdPow s = ⊥) (hz : CH.d _ 2 (zK Λ s) = 0) (hz' : CH.d _ 2 (zK Λ' s) = 0) :
    (CH.cx _).cls (zK Λ s) hz = (CH.cx _).cls (zK Λ' s) hz' := _root_.GlobalTheory.CompanionTheory.ConeZcls.main Λ Λ' s hs hz hz'


omit [CharZero K] in
theorem zK_precomp {C C' : Type 1} [Category.{0} C] [Category.{0} C'] {g : C ⥤ Thick (smFun X q)} {D : E.LineData X}
    (Λ : CLiftK g D) (h : C' ⥤ C) (s : ℕ) :
    zK (Λ.precomp h) s = (CH.Mor.restrict (g ⋙ O (smFun X q)) h).pullC 2 (zK Λ s) := by
  funext σ
  rfl

end K

theorem lift_exists {K : Type} [CommRing K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (D : E.LineData X)
    (s : ℕ) : Nonempty (CLiftK (KS q s (𝒱D D)).ι D) := _root_.GlobalTheory.CompanionTheory.ConeLiftEx.nonempty_cLiftK q D s

theorem sSup_𝒱D {R : Type} [CommRing R] {X : Scheme.{0}} (D : E.LineData X) (N : ℕ)
    (i : X ⟶ ReciprocityTheory.ChartRestriction.G.Geo.Tor.PSpace R N) (h : IsTautologicalLineAt D N i) : sSup (𝒱D D) = ⊤ := _root_.GlobalTheory.CompanionTheory.ConeCover.main D N i h

end CrystallineSemistableComparison.Pb
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.RSubOneMem =====
