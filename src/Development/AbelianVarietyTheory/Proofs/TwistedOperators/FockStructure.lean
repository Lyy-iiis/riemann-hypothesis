module

public import Development.AbelianVarietyTheory.Definitions.Foundations.IsFockIPOfFockData
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankFockJointHarmonicsHighestWeightOfShape
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FischerDecompositionFockNoncompactParts
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockHarmonicHomogeneousOfKType
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockJointHarmonicsHighestWeightEqBotOfNotShape
public import Formalism.LocalRingCardinality.DataTheta
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightDegreeLeOfHomogeneousFockWeightVector
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init
import Mathlib.Tactic.Basify
import Std.Tactic.BVDecide.Normalize.Prop

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankFockJointHarmonicsHighestWeightOfShapeStatement, Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockStructure

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankFockJointHarmonicsHighestWeightOfShapeStatement =====
section -- clump:auto
@[expose] public section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial

theorem _root_.GlobalTheory.T.finrank_fockJointHarmonics_highestWeight_of_shape : ∀ (p q r s : ℕ) (μ : Ix p q → ℚ) (μ' : Ix r s → ℚ), JointShape p q r s μ μ' → Module.finrank ℂ ↥(hwSub (fockAct1 p q r s) μ ⊓ hwSub (fockAct2 p q r s) μ' ⊓ Submodule.span ℂ (jointHarm p q r s)) = 1 := by
  first | exact @GlobalTheory.JointHarm.finrank_joint_highest_of_shape
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankFockJointHarmonicsHighestWeightOfShapeStatement =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockStructure =====
section -- clump:auto
@[expose] public section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg

namespace GlobalTheory.FockAlg

theorem fock_structure : ∀ X : ProvA, admH2 X := by
  intro X p q r s
  refine ⟨fun d μ P hP hw => (_root_.GlobalTheory.FockAlg.degW_le_of_homog_wtSub p q r s).1 d μ P hP hw.1 hw.2.1,
    fun d μ P hP hw => (_root_.GlobalTheory.FockAlg.degW_le_of_homog_wtSub p q r s).2 d μ P hP hw.1 hw.2.1,
    fun μ P h0 ht hh => (_root_.GlobalTheory.FockAlg.harmonic_homog_of_type p q r s).1 μ P h0 ht hh,
    fun μ P h0 ht hh => (_root_.GlobalTheory.FockAlg.harmonic_homog_of_type p q r s).2 μ P h0 ht hh,
    fun μ μ' => ⟨GlobalTheory.T.finrank_fockJointHarmonics_highestWeight_of_shape p q r s μ μ', _root_.GlobalTheory.FockAlg.jointHarm_hw_eq_bot p q r s μ μ'⟩, ?_⟩
  intro u1 u2 hu d
  obtain ⟨h1, h2, h3⟩ := _root_.GlobalTheory.FischerParts.fischer_parts p q r s d
  cases u1 <;> cases u2
  · simp at hu
  · have e1 : lowKer X (X.fock p q r s) false true = harm1 p q r s := by
      ext P; simp [lowKer, harm1, FockData.act2]
    have e2 : raised X (X.fock p q r s) false true d = {R | ∃ Q ∈ homog (Ix p q × Ix r s) d,
        ∃ Z : Mat r s, IsPC Z ∧ R = plusPart (fockAct2 p q r s Z) Q} := by
      ext P; simp [raised, FockData.act2]
    rw [e1, e2]; exact h2
  · have e1 : lowKer X (X.fock p q r s) true false = harm2 p q r s := by
      ext P; simp [lowKer, harm2, FockData.act1]
    have e2 : raised X (X.fock p q r s) true false d = {R | ∃ Q ∈ homog (Ix p q × Ix r s) d,
        ∃ Z : Mat p q, IsPC Z ∧ R = plusPart (fockAct1 p q r s Z) Q} := by
      ext P; simp [raised, FockData.act1]
    rw [e1, e2]; exact h1
  · have e1 : lowKer X (X.fock p q r s) true true = jointHarm p q r s := by
      ext P; simp [lowKer, jointHarm, harm1, harm2, FockData.act1, FockData.act2]
    have e2 : raised X (X.fock p q r s) true true d = {R | ∃ Q ∈ homog (Ix p q × Ix r s) d,
        (∃ Z : Mat p q, IsPC Z ∧ R = plusPart (fockAct1 p q r s Z) Q) ∨
          ∃ Z : Mat r s, IsPC Z ∧ R = plusPart (fockAct2 p q r s Z) Q} := by
      ext P; simp [raised, FockData.act1, FockData.act2]
    rw [e1, e2]; exact h3

end GlobalTheory.FockAlg
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockStructure =====
