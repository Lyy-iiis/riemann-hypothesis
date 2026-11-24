module

public import Mathlib.Algebra.Group.End
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.EquivFin
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.LSegJacquet
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetMultiplicityPos
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PrincipalSeriesSupport.PrinSeriesWord
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SupportSubschemeEmbedding
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.BernsteinZelevinskyFiniteness
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.GeometricLemma
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.HasSupportOfIsSubquotientProdIrr
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
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.FineJacquetModules.SegDefs

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CardFiber, Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IrreducibleSubquotientCuspidalPermutation

-- ===== clump member: Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CardFiber =====
section -- clump:auto
@[expose] public section

namespace MultisetMapEqExistsEquivPerm

private lemma card_fiber {α : Type*} [DecidableEq α] {l : ℕ} (x : Fin l → α) (v : α) :
    Fintype.card {a : Fin l // x a = v} =
      (Multiset.map x Finset.univ.val).countP (fun b => b = v) := by
  rw [Multiset.countP_map, Fintype.card_subtype]
  rfl

end MultisetMapEqExistsEquivPerm

theorem UpperTheory.Reformulated.B.Yhb6.main.{u_1} :
    ∀ {α : Type u_1} {l : ℕ} {x y : Fin l → α},
      Multiset.map y Finset.univ.val = Multiset.map x Finset.univ.val →
        ∃ (e : Equiv.Perm (Fin l)), ∀ (a : Fin l), y a = x ((e : Fin l → Fin l) a) := by
  intro α l x y h
  classical
  have hc : ∀ v : α, Fintype.card {a : Fin l // y a = v} = Fintype.card {a : Fin l // x a = v} := by
    intro v
    convert (MultisetMapEqExistsEquivPerm.card_fiber y v).trans
      ((congrArg (fun m => Multiset.countP (fun b => b = v) m) h).trans (MultisetMapEqExistsEquivPerm.card_fiber x v).symm)
  let E : ∀ v : α, {a : Fin l // y a = v} ≃ {a : Fin l // x a = v} :=
    fun v => Fintype.equivOfCardEq (hc v)
  refine ⟨Equiv.ofFiberEquiv E, fun a => ?_⟩
  exact (Equiv.ofFiberEquiv_map E a).symm
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CardFiber =====

-- ===== clump member: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IrreducibleSubquotientCuspidalPermutation =====
section -- clump:auto
@[expose] public section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg

namespace GlobalTheory.CompanionTheory.SegNcjm

theorem exists_perm_one_le_jm : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {l N : ℕ} (x : Fin l → IrrGL (k := k))
    (hx : ∑ a, (x a).1 = N) (hxc : ∀ a, (x a).IsCusp) {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) k) V) (hs : IsSmooth π) (hi : π.IsIrreducible)
    (h : IsSubquotient π (prodIrr x hx)),
    ∃ (e : Equiv.Perm (Fin l)) (he : ∑ a, (x (e a)).1 = N), 1 ≤ jm (fun a => x (e a)) he π := by
  intro k _ _ _ _ hA l N x hx hxc V _ _ π hs hi h
  obtain ⟨c, y, hy, hyc, φ, hφ⟩ := _root_.GlobalTheory.CompanionTheory.SubEmb.subEmbedding k N V π hs hi
  have h1 : HasSupport π (Finset.univ.val.map x) := hasSupport_of_isSubquotient hi hxc h
  have h2 : HasSupport π (Finset.univ.val.map y) := hasSupport_of_isSubquotient hi hyc (.of_injective φ hφ)
  have hm := GlobalTheory.CompanionTheory.Hypotheses₂.TD.hasSupport_unique GlobalTheory.CompanionTheory.GeoLink.geometricLemma
    GlobalTheory.CompanionTheory.Published.bernsteinZelevinskyFiniteness h2 h1
  have hcl : c = l := by simpa using congrArg Multiset.card hm
  subst hcl
  obtain ⟨e, he⟩ := _root_.UpperTheory.Reformulated.B.Yhb6.main hm
  obtain rfl : y = fun a => x (e a) := funext he
  refine ⟨e, hy, GlobalTheory.CompanionTheory.FrobJm.one_le_jm hA _ hy π hs φ ?_⟩
  have : Nontrivial V := GlobalTheory.SmGL.nontrivial_of_irreducible hi
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  exact ⟨v, fun h0 => hv (hφ (h0.trans (map_zero φ).symm))⟩

end GlobalTheory.CompanionTheory.SegNcjm
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IrreducibleSubquotientCuspidalPermutation =====
