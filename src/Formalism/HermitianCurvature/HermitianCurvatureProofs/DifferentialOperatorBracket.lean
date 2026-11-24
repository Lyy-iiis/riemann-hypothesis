module

public import Formalism.HermitianCurvature.StatementQ
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CapelliTwoByTwo
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.QuadraticFormTwoTwo.RadialDecompositionOfParts
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.RightTypeAction
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QnTPres
public import Formalism.HermitianCurvature.FrameExists2
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ExistsFrameTwo
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.FrameCompletion
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.FrameExtension
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.GroupGeneratedByExp
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.HermitianFormRankFour
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.IrreducibleCapelliModules
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LieBracketMultiplication
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LieListProducts
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ProductIntervalFrames
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LemmaDDeterminantIdentity
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Formalism.HermitianCurvature.HermitianCurvatureProofs.RadialDecompositionSpectralOfBranching, Formalism.HermitianCurvature.HermitianCurvatureProofs.DifferentialOperatorBracket

-- ===== clump member: Formalism.HermitianCurvature.HermitianCurvatureProofs.RadialDecompositionSpectralOfBranching =====
section -- clump:auto
@[expose] public section

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q

theorem radialDecompositionSpectral_of_branching : Branching → RadialDecompositionSpectral := fun hB =>
  _root_.Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors.radial_decomposition_of_parts' second_contraction_adapted contractions_covariant capelli_two_by_two
    right_type_action hB qnTPres

end Formalism.FourierDecayAlt.P
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.HermitianCurvature.HermitianCurvatureProofs.RadialDecompositionSpectralOfBranching =====

-- ===== clump member: Formalism.HermitianCurvature.HermitianCurvatureProofs.DifferentialOperatorBracket =====
section -- clump:auto
@[expose] public section

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q

theorem differential_operator_linear : Qr.DOpLin := qr_dOpLin_of trotter_product_formula trotter_product_matrices representation_exp

theorem differential_operator_bracket : Qr.DOpBracket := qr_dOpBracket_of representation_exp differential_operator_linear differential_operator_adjoint

theorem elementary_lie_elements : Qr.EcLie := qr_ecLie_of differential_operator_linear differential_operator_bracket

theorem frame_general_linear : Qr.FrameGl := qr_frameGl_of elementary_lie_elements

theorem lie_stabilizer : Qr.LieStab := qr_lieStab_of exp_generates representation_exp elementary_lie_elements

theorem qr_frameChange_proof : Qr.FrameChange := qr_frameChange_of elementary_lie_elements frame_general_linear

theorem branching_compact : Qr.BranchingK :=
  qr_branchingK_of branching_algebraic frame_general_linear lie_stabilizer stabilizer_lie_algebra qr_frameChange_proof
    exists_frame_two

theorem branching_proof : Branching := qr_branching_of branching_compact

theorem spectral_two_by_two : RadialDecompositionSpectral := radialDecompositionSpectral_of_branching branching_proof

end Formalism.FourierDecayAlt.P
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.HermitianCurvature.HermitianCurvatureProofs.DifferentialOperatorBracket =====
