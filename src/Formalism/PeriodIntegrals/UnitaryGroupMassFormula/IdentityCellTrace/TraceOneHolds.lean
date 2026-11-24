module

public import Formalism.PeriodIntegrals.CMTraceOnto
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CMTraceSurjective.IsTrMulConjOfMem
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdentityCellTrace.TermIdIffInSOf
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
import Mathlib.Tactic.Linter.HaveILetI

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Formalism.PeriodIntegrals.OrbitalBoundsConclusion.CMTraceOnto, Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdentityCellTrace.TraceOneHolds

-- ===== clump member: Formalism.PeriodIntegrals.OrbitalBoundsConclusion.CMTraceOnto =====
section -- clump:auto
@[expose] public section

end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.PeriodIntegrals.OrbitalBoundsConclusion.CMTraceOnto =====

-- ===== clump member: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdentityCellTrace.TraceOneHolds =====
section -- clump:auto
@[expose] public section

noncomputable section

open NumberField Formalism.BasicNotions

namespace PI.UnitaryGroupMassFormula.IdCellInSW

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem traceOne_holds (D : D7) : TraceOne D := by
  haveI : NumberField.IsCMField D.host.E := D.host.isCMField_hostE

  have hgal := (D.host.der.conj_iff D.host.φ₀ ((NumberField.IsCMField.complexConj D.host.E).restrictScalars ℚ)).mp (fun x =>
    NumberField.ComplexEmbedding.IsConj.eq (NumberField.IsCMField.isConj_complexConj D.host.E D.host.φ₀) x)
  have hc : ∀ x : D.host.E, D.host.conj x = star x := by
    intro x
    unfold Formalism.HC.HostRaw.conj
    rw [← hgal, MulEquiv.symm_apply_apply]
    rfl
  have hU : PI.IsCMUnram D.host.E := by
    refine ⟨?_, ?_, ?_⟩
    · infer_instance
    · intro ψ a
      exact NumberField.ComplexEmbedding.IsConj.eq (NumberField.IsCMField.isConj_complexConj D.host.E ψ) a
    · intro P hP
      have hne : P ≠ ⊥ :=
        Ring.ne_bot_of_isMaximal_of_not_isField hP (NumberField.RingOfIntegers.not_isField D.host.E)
      have h := D.host.der.unramEF P hP.isPrime hne
      push_neg at h
      obtain ⟨x, hx⟩ := h
      refine ⟨x, D.host.conj • x, ?_, ?_⟩
      · rw [← hc]
        rfl
      · intro hmem
        apply hx
        rw [← neg_sub]
        exact P.neg_mem hmem
  obtain ⟨x, y, hy, hxy⟩ := _root_.PI.CMT.main D.host.E hU 1 (by simp)
  exact ⟨x, by
    simpa [← hy] using congrArg (fun z : 𝓞 D.host.E => (z : D.host.E)) hxy⟩

end PI.UnitaryGroupMassFormula.IdCellInSW
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdentityCellTrace.TraceOneHolds =====
