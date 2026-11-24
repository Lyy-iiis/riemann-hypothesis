module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.DiscreteSeriesTopClasses.IsInvOne
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Development.AbelianVarietyTheory.Definitions.Foundations.ContinuousOfMemCcSmooth
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
import Development.AbelianVarietyTheory.Definitions.Foundations.MeasurePreservingRmulQuotMeas

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.WeilBound.RepresentationTheoryGL.StandardBasisDerivatives.ArchimedeanBasisDerivatives.StBasDeriv, Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.DiscreteSeriesTopClasses.StTopClass

-- ===== clump member: Development.WeilBound.RepresentationTheoryGL.StandardBasisDerivatives.ArchimedeanBasisDerivatives.StBasDeriv =====
section -- clump:auto
@[expose] public section

noncomputable section

open MvPolynomial
open scoped ContDiff

namespace PositivityTheory.Rg.Pc1

variable {n : ℕ}

def IsProfile (N : ℕ) (G : ℝ → ℝ) : Prop :=
  ContDiff ℝ ∞ G ∧ (∀ x, 1 ≤ x → G x = 0) ∧ (∀ x, 0 ≤ (-1) ^ N * iteratedDeriv N G x) ∧ iteratedDeriv N G 0 ≠ 0

end PositivityTheory.Rg.Pc1
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.WeilBound.RepresentationTheoryGL.StandardBasisDerivatives.ArchimedeanBasisDerivatives.StBasDeriv =====

-- ===== clump member: Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.DiscreteSeriesTopClasses.StTopClass =====
section -- clump:auto
@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Matrix GlobalTheory.Orb GlobalTheory.OpTrace GlobalTheory.AutomorphicL2Unitary
open PositivityTheory.Rg.Pc1 (IsProfile)

namespace PositivityTheory.RgTw

variable {n : ℕ}

def KU (n : ℕ) : Subgroup (G n) where
  carrier := {k | th k = k}
  one_mem' := th_one
  mul_mem' := fun {x y} hx hy => by
    simp only [Set.mem_ofPred_eq, th, star_mul, _root_.mul_inv_rev] at *
    rw [hx, hy]
  inv_mem' := fun {x} hx => by
    simp only [Set.mem_ofPred_eq, th, star_inv] at *
    rw [hx]

section

variable (n) [MeasurableSpace (G n)] [BorelSpace (G n)]

def IsThetaOp {U : Type} [NormedAddCommGroup U] [InnerProductSpace ℂ U] (π : G n →* (U →L[ℂ] U)) (A : U →L[ℂ] U) : Prop :=
  (∀ v, ‖A v‖ = ‖v‖) ∧ Function.Surjective A ∧ ∀ x, A ∘L π x = π (th x) ∘L A

end

end PositivityTheory.RgTw
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.DiscreteSeriesTopClasses.StTopClass =====
