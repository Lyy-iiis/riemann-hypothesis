module

public import ReciprocityTheory.AnalyticForms.RegularLocalRings.ProjHypA
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.ProjDehom
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinTypeQE
public import Mathlib.AlgebraicGeometry.Noetherian
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.ProjHypC
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Algebra.AffineMonoid.UniqueSums
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Linter.HaveILetI

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: ReciprocityTheory.AnalyticForms.RegularLocalRings.ProjHypStalk, ReciprocityTheory.AnalyticForms.RegularLocalRings.ProjHyp

-- ===== clump member: ReciprocityTheory.AnalyticForms.RegularLocalRings.ProjHypStalk =====
section -- clump:auto
@[expose] public section

namespace ReciprocityTheory.AnForm.R

open MvPolynomial AlgebraicGeometry CategoryTheory

noncomputable section

section Loc

variable {σ : Type}

def kerPt (z : σ → ℂ) : Ideal (MvPolynomial σ ℂ) :=
  RingHom.ker (MvPolynomial.eval z : MvPolynomial σ ℂ →+* ℂ)

instance kerPt_isPrime (z : σ → ℂ) : (kerPt z).IsPrime :=
  RingHom.ker_isPrime _

end Loc

variable {K : Type} [Fintype K] [Nonempty K] {ι : K → Type} [∀ k, Fintype (ι k)]

end

end ReciprocityTheory.AnForm.R
end -- clump:auto
end -- clump:auto
-- ===== end clump member: ReciprocityTheory.AnalyticForms.RegularLocalRings.ProjHypStalk =====

-- ===== clump member: ReciprocityTheory.AnalyticForms.RegularLocalRings.ProjHyp =====
section -- clump:auto
@[expose] public section

namespace ReciprocityTheory.AnForm.R

open MvPolynomial AlgebraicGeometry CategoryTheory

noncomputable section

variable {K : Type} [Fintype K] [Nonempty K] {ι : K → Type} [∀ k, Fintype (ι k)]

instance isNoetherian_projX {P : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (hP : IsMultiHomogIdeal P) :
    IsNoetherian (projX P hP) :=
  (isNoetherian_iff_of_finite_iSup_eq_top (S := chartOpen hP) (iSup_chartOpen_eq_top hP)).mpr
    (isNoetherianRing_gammaChart hP)

def projB (P D : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (hP : IsMultiHomogIdeal P) :
    TopologicalSpace.Closeds (projX P hP) :=
  letI := segreGraded hP
  ⟨ProjectiveSpectrum.zeroLocus (segreGrading P) (Ideal.Quotient.mk (segreIdeal P) '' (segreIdeal D : Set _)),
    ProjectiveSpectrum.isClosed_zeroLocus _ _⟩

def ptIdealOf {σ : Type} (z : σ → ℂ) : Ideal (MvPolynomial σ ℂ) :=
  RingHom.ker (MvPolynomial.eval z : MvPolynomial σ ℂ →+* ℂ)

instance ptIdealOf_isPrime {σ : Type} (z : σ → ℂ) : (ptIdealOf z).IsPrime :=
  RingHom.ker_isPrime _

abbrev locAt {σ : Type} (I : Ideal (MvPolynomial σ ℂ)) (z : σ → ℂ) : Type :=
  Localization.AtPrime (ptIdealOf z) ⧸
    Ideal.map (algebraMap (MvPolynomial σ ℂ) (Localization.AtPrime (ptIdealOf z))) I

end

end ReciprocityTheory.AnForm.R
end -- clump:auto
end -- clump:auto
-- ===== end clump member: ReciprocityTheory.AnalyticForms.RegularLocalRings.ProjHyp =====
