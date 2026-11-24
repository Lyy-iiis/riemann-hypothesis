module

public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsSemilocalLengthSum
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PFibreFinite
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PFiniteAlgebraLengthSum
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PSemilocalLengthSum
public import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.FieldNumbersLocalIntegralClosureFinite
public import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.FieldNumbersSemilocalMaxIdeals
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsSemilocalLength
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PDivCycleMinimal
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PFibreRelDim
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PSemilocalLength
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsDivPushForwardLocal
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PDivPushForwardLocal
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsDivPushForward
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PContractRelDimLe
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PDivPushForward
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Statements
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Assembly
import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.HilbertSamuelIrreducibleBasicOpenConnected
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
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PPFDegree

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.FieldNumbersSemilocalLengthSum, GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.FieldNumbersSemilocalLength, GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.FieldNumbersDivPushForwardLocal, GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.NumbersDVRFlagBundleLineBase, GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.FieldNumbersProjectionFormulaDegree

-- ===== clump member: GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.FieldNumbersSemilocalLengthSum =====
section -- clump:auto
@[expose] public section

set_option maxSynthPendingDepth 1

theorem GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_SemilocalLengthSum.{u} : GroundTheory.Heights₂.Heights.FieldNumbers.SemilocalLengthSum.Statement.{u} :=
  @GroundTheory.Heights₂.Heights.FieldNumbers.SemilocalLengthSum.proof.{u} GroundTheory.Heights₂.Heights.FieldNumbers.FibreFinite.proof GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_SemilocalFiniteRank GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_DegZeroLocalRing GroundTheory.Heights₂.Heights.FieldNumbers.FiniteAlgebraLengthSum.proof GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_SemilocalMaxIdeals
end -- clump:auto
end -- clump:auto
-- ===== end clump member: GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.FieldNumbersSemilocalLengthSum =====

-- ===== clump member: GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.FieldNumbersSemilocalLength =====
section -- clump:auto
@[expose] public section

set_option maxSynthPendingDepth 1

theorem GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_SemilocalLength.{u} : GroundTheory.Heights₂.Heights.FieldNumbers.SemilocalLength.Statement.{u} :=
  @GroundTheory.Heights₂.Heights.FieldNumbers.SemilocalLength.proof.{u} GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_SemilocalLengthSum GroundTheory.Heights₂.Heights.FieldNumbers.FibreRelDim.proof GroundTheory.Heights₂.Heights.FieldNumbers.DivCycleMinimal.proof GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_ConeLocalLength
end -- clump:auto
end -- clump:auto
-- ===== end clump member: GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.FieldNumbersSemilocalLength =====

-- ===== clump member: GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.FieldNumbersDivPushForwardLocal =====
section -- clump:auto
@[expose] public section

set_option maxSynthPendingDepth 1

theorem GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_DivPushForwardLocal.{u} : GroundTheory.Heights₂.Heights.FieldNumbers.DivPushForwardLocal.Statement.{u} :=
  @GroundTheory.Heights₂.Heights.FieldNumbers.DivPushForwardLocal.proof.{u} GroundTheory.Heights₂.Heights.FieldNumbers.DivCycleMinimal.proof GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_ConeLocalLength GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_DegZeroLocalRing GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_SemilocalFiniteRank GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_SemilocalLength
end -- clump:auto
end -- clump:auto
-- ===== end clump member: GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.FieldNumbersDivPushForwardLocal =====

-- ===== clump member: GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.NumbersDVRFlagBundleLineBase =====
section -- clump:auto
@[expose] public section

set_option maxSynthPendingDepth 1

theorem GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_DivPushForward.{u} : GroundTheory.Heights₂.Heights.FieldNumbers.DivPushForward.Statement.{u} :=
  @GroundTheory.Heights₂.Heights.FieldNumbers.DivPushForward.proof.{u} GroundTheory.Heights₂.Heights.FieldNumbers.ContractRelDimLe.proof GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_DivPushForwardLocal
end -- clump:auto
end -- clump:auto
-- ===== end clump member: GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.NumbersDVRFlagBundleLineBase =====

-- ===== clump member: GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.FieldNumbersProjectionFormulaDegree =====
section -- clump:auto
@[expose] public section

set_option maxSynthPendingDepth 1

theorem GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_ProjectionFormulaDegree.{u} : GroundTheory.Heights₂.Heights.FieldNumbers.ProjectionFormulaDegree.Statement.{u} :=
  @GroundTheory.Heights₂.Heights.FieldNumbers.ProjectionFormulaDegree.proof.{u} GroundTheory.Heights₂.Heights.FieldNumbers.CutRational.full GroundTheory.Heights₂.Heights.FieldNumbers.IntNumBase.full GroundTheory.Heights₂.Heights.FieldNumbers.ProjectionFormulaContracted.full GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_DivPushForward
end -- clump:auto
end -- clump:auto
-- ===== end clump member: GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.FieldNumbersProjectionFormulaDegree =====
