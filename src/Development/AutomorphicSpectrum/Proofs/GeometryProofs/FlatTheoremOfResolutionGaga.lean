module

public import Development.AutomorphicSpectrum.Statements.GeometryStatements.FinConstFor
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FiniteConstantAllHolds
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.ThmFlatA
public import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.GagaSections
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.CardComapMulFinsumEqFinsumFibres
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlatFirstFromResolutionAndGaga
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatLineGenerator
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlatTheoremOfParts
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlatZeroFromResolutionAndGaga
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AutomorphicSpectrum.Proofs.GeometryProofs.FiniteConstantHolds, Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlatTheoremOfResolutionGaga

-- ===== clump member: Development.AutomorphicSpectrum.Proofs.GeometryProofs.FiniteConstantHolds =====
section -- clump:auto
@[expose] public section

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem finConst_of_all_hosts : FinConst :=
  FinConstAll.finConst _root_.GlobalTheory.CompanionTheory.Ar.Flat.FinAll.finConstAll

end GlobalTheory.CompanionTheory.Ar.Flat
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AutomorphicSpectrum.Proofs.GeometryProofs.FiniteConstantHolds =====

-- ===== clump member: Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlatTheoremOfResolutionGaga =====
section -- clump:auto
@[expose] public section

open CategoryTheory AlgebraicGeometry NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.HT GlobalTheory.CompanionTheory.Ar.Flat ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem thmFlatA_of_resK_gaga_partI :
    Geo.ResK.ResKStatement → GagaSections → PartI → ThmFlatA :=
  fun hR hG hP =>
    _root_.GlobalTheory.CompanionTheory.Ar.Flat.thmFlatA_of_parts hP (_root_.GlobalTheory.CompanionTheory.Ar.Flat.A0.flat_zero_of_resolution_gaga hR hG) (_root_.GlobalTheory.CompanionTheory.Ar.Flat.FlatFirstTheorem.flat_first_of_resolution_gaga hR hG) _root_.GlobalTheory.CompanionTheory.Ar.Flat.finConst_of_all_hosts

end GlobalTheory.CompanionTheory.Ar.Flat
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlatTheoremOfResolutionGaga =====
