module

public import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.NormCharSplit
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.ComplexBaseChangeOfLiterature
public import Development.AutomorphicArithmetic.Foundations.Convolution.NormCharacterPowers.NormCharPowHolds
public import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.LocHeckeInert
public import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.CoreDesc
public import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.CoreLift
public import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.DescStep
public import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.LiftAll
public import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.LiftStep
public import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.SplitStrong
public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.IntegralUnitBaseChange.InvTransposeGLInvTransposeGL
public import Development.AutomorphicArithmetic.Foundations.Convolution.BlockEvaluation.Ci
public import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.GmOfBcfl
public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.IntegralUnitBaseChange.BcflUnit
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import PositivityTheory.AutomorphicForms.PublishedInputs.CyclicBaseChange.PSSmo
import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.Places

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.Cbcc, Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.CbccOfCore, Development.AutomorphicArithmetic.Foundations.Convolution.CbccOfUnit, Development.AutomorphicArithmetic.Foundations.Convolution.Cbcc

-- ===== clump member: Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.Cbcc =====
section -- clump:auto
@[expose] public section

open NumberField in
private alias not_both := _root_.UpperTheory.CBC.SmoothnessOfSatakeParameters.not_both

open NumberField in
theorem UpperTheory.ConvolutionTheory.T.cbcc :
    UpperTheory.ConvolutionTheory.T.Places → UpperTheory.ConvolutionTheory.T.LiftStep → UpperTheory.ConvolutionTheory.T.LiftAll → UpperTheory.ConvolutionTheory.T.DescStep → UpperTheory.ConvolutionTheory.T.SplitStrong → UpperTheory.V.Z.Bc.CBCc := by
  intro hPl hLS hLA hDS hSS K M _ _ _ _ _ _ hp hK n hn
  haveI := hK
  haveI hM : IsTotallyComplex M := isTotallyComplex_of_algebra K M
  haveI : Fact (Module.finrank K M).Prime := ⟨hp⟩
  haveI : FiniteDimensional K M := Module.finite_of_finrank_pos hp.pos
  haveI : IsCyclic (M ≃ₐ[K] M) := isCyclic_of_prime_card (IsGalois.card_aut_eq_finrank K M)
  obtain ⟨σ, hσ⟩ := IsCyclic.exists_generator (α := M ≃ₐ[K] M)
  refine ⟨fun π => ?_, fun P hP => ?_, fun π P _ hw => UpperTheory.ConvolutionTheory.R.fibre_holds K M hp n hn π P hw⟩
  · rcases π with @⟨_, π⟩ | @⟨hR, π⟩
    swap
    · exact (not_both K hR hK).elim
    rcases hLS K M σ hσ hp n hn (fun m hm _ => hLA K M σ hσ hp m hm) π with ⟨ι, _, m, Q, hm, h2, hw⟩ | ⟨P, ⟨h1, h2⟩, h3⟩
    · obtain ⟨η, hη, e⟩ := UpperTheory.ConvolutionTheory.R.twoParts_holds K M hp n _ ι m Q hn hm h2 hw
      exact Or.inl ⟨η, hη, Quotient.exact e⟩
    · exact Or.inr ⟨.cx P, h1, fun τ m h => (h2 τ m).1 h, hSS K M σ hσ hp n hn π P h3 h1⟩
  · rcases P with @⟨_, P⟩ | @⟨hR, P⟩
    swap
    · exact (not_both M hR hM).elim
    obtain ⟨hinf, -, hne, -⟩ := hPl K M hp
    obtain ⟨v, hv⟩ := hinf.nonempty
    obtain ⟨w⟩ := hne v
    obtain ⟨π, ⟨h1, h2⟩, -⟩ := hDS K M σ hσ hp n hn P hP v w hv
    exact ⟨.cx π, h1, fun τ m h => (h2 τ m).2 h, hSS K M σ hσ hp n hn π P hP h1⟩
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.Cbcc =====

-- ===== clump member: Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.CbccOfCore =====
section -- clump:auto
@[expose] public section

theorem UpperTheory.ConvolutionTheory.T.cbcc_of_core (hC : UpperTheory.ConvolutionTheory.CI) (hG : UpperTheory.ConvolutionTheory.GM.GM) : UpperTheory.V.Z.Bc.CBCc :=
  have a := liftStep (coreLift hC hG)
  have b := liftAll a
  have c := descStep (coreDesc hC hG) b
  cbcc places a b c (splitStrong c)
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.CbccOfCore =====

-- ===== clump member: Development.AutomorphicArithmetic.Foundations.Convolution.CbccOfUnit =====
section -- clump:auto
@[expose] public section

theorem UpperTheory.ConvolutionTheory.cbcc_of_unit (h : PositivityTheory.Rg.Tf.Loc.BCFLUnit) : UpperTheory.V.Z.Bc.CBCc :=
  UpperTheory.ConvolutionTheory.T.cbcc_of_core UpperTheory.ConvolutionTheory.ci (UpperTheory.ConvolutionTheory.GM.gm_of_bcfl h)
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AutomorphicArithmetic.Foundations.Convolution.CbccOfUnit =====

-- ===== clump member: Development.AutomorphicArithmetic.Foundations.Convolution.Cbcc =====
section -- clump:auto
@[expose] public section

theorem UpperTheory.ConvolutionTheory.cbcc : UpperTheory.V.Z.Bc.CBCc :=
  UpperTheory.ConvolutionTheory.cbcc_of_unit PositivityTheory.Rg.Tf.Loc.bcflUnit
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AutomorphicArithmetic.Foundations.Convolution.Cbcc =====
