import LeechNorm208Layers
import LeechNorm192Layers
import LeechNorm176Layers
import LeechNorm160Layers
import LeechNorm144Layers
import LeechNorm128Layers
import LeechNorm112Layers
import RiemannHypothesisRoute
import LeechNorm96Layers
import LeechNorm80Layers
import LeechNorm64Layers
import LeechNorm80
import LeechLayers
import LeechNorm48
import LeechNorm48Pairs
import LeechShellPairs
import LeechCoordinateFrames
import ConwayMoves
import ConwayTransitivity
import ConwayCoordinates
import ConwayGenerators
import ConwayTally
import ConwayNeighborCount
import ConwayPairs
import ConwayStabilizer
import ConwayOrder
import Poincare
import PathSix
import Wirtinger
import LoopWirtinger
import WirtingerStore
import Gap
import GapMirror
import GapMirrorCalculus
import GapMirrorBridge
import RingGapBridge
import FourDotGapBridge
import TwoWaveGapBridge
import TwoWaveDiscreteGapBridge
import TwoWaveFlipBridge
import TwoWaveReadoutObstruction
import Isoperimetric
import RingDecay
import RingSumMinusTwelfth
import RamanujanGap
import GapCrossing
import GapWaveTail
import HarperSquash
import Polygon
import CubeCheeger
import Bridges
import Torus
import WallPush
import Harper
import Unify
import GolayMatrixDistance
import EdgeOptimal
import E8PlumbingBridge
import E8Tab30Bridge
import HammingCode
import PlumbingStick
import PlumbingHelp
import E8CostMirror
import GolayLeechBridge
import LeechLattice
import LeechKissing
import PlaygroundLeech
import LeechBasis
import LeechThreeE8Cosets
import LeechFrameStabilizer
import LeechSextet
import MathieuGroup
import MathieuBase
import LightBounceAndCapture

/-! Each line must list only `propext`, `Classical.choice` and `Quot.sound` (some list fewer). Any `sorryAx` or any other axiom means the check fails. -/

#print axioms DiscretePoincare.telescope
#print axioms DiscretePoincare.step_bound
#print axioms DiscretePoincare.pair_sum
#print axioms DiscretePoincare.poincare
#print axioms DiscretePoincare.mean_has_no_gap
#print axioms PathSix.sqrt_three_bounds
#print axioms PathSix.gap_pos
#print axioms PathSix.mass_nonneg
#print axioms PathSix.symmetric_bound
#print axioms PathSix.antisymmetric_identity
#print axioms PathSix.antisymmetric_bound
#print axioms PathSix.poincare
#print axioms PathSix.mode_mean_zero
#print axioms PathSix.mode_mass_pos
#print axioms PathSix.mode_equality
#print axioms PathSix.sharp
#print axioms PathSix.valid_bound_iff
#print axioms PathSix.gap_decimal_bounds
#print axioms PathSix.display_rounding_bin
#print axioms PathSix.display_exceeds_gap
#print axioms PathSix.rounded_value_not_valid_bound
#print axioms CycleWirtinger.ortho
#print axioms CycleWirtinger.conj_e
#print axioms CycleWirtinger.e_eq_exp
#print axioms CycleWirtinger.normSq_e_sub_one
#print axioms CycleWirtinger.normSq_e_neg_sub_one
#print axioms CycleWirtinger.cos_step
#print axioms CycleWirtinger.cos_le
#print axioms CycleWirtinger.fourier_neg
#print axioms CycleWirtinger.parseval
#print axioms CycleWirtinger.parseval_real
#print axioms CycleWirtinger.fourier_step
#print axioms CycleWirtinger.wirtinger
#print axioms CycleWirtinger.re_sq
#print axioms CycleWirtinger.sum_re_sq
#print axioms CycleWirtinger.wirtinger_sharp
#print axioms HugGap.lin_deriv
#print axioms HugGap.keep_deriv
#print axioms HugGap.keep_unbounded
#print axioms HugGap.breathe_deriv
#print axioms HugGap.breathe_levels
#print axioms HugGap.breathe_bounded
#print axioms HugGap.finite_iff_gap
#print axioms HugGap.chain_store_deriv
#print axioms HugGap.gap_beats_every_power
#print axioms HugGap.power_decay_fails_rule
#print axioms HugGap.input_ended
#print axioms HugGap.steady_input_stays
#print axioms HugGap.breath_keeps_four_fifths
#print axioms HugGap.breath_out_is_a_gap
#print axioms GapMirror.step_one
#print axioms GapMirror.step_step
#print axioms GapMirror.step_change
#print axioms GapMirror.edge
#print axioms GapMirror.rate_mirror
#print axioms GapMirror.z_step
#print axioms GapMirror.z_mirror
#print axioms GapMirror.mirror_ne_zero
#print axioms GapMirror.mirror_sum
#print axioms GapMirror.mirror_step
#print axioms GapMirror.blow_factor
#print axioms GapMirror.blow_shape
#print axioms GapMirror.finite_before
#print axioms GapMirror.blows_up
#print axioms GapMirror.mirror_time
#print axioms GapMirror.below_denominator
#print axioms GapMirror.below_positive
#print axioms GapMirror.below_never_grows
#print axioms GapMirror.below_fades
#print axioms GapMirrorCalculus.z_grows
#print axioms GapMirrorCalculus.z_mirror
#print axioms GapMirrorCalculus.bump_zero
#print axioms GapMirrorCalculus.bump_solves
#print axioms GapMirrorCalculus.edge
#print axioms GapMirrorCalculus.fades
#print axioms GapMirrorCalculus.blow_at
#print axioms GapMirrorCalculus.finite_before
#print axioms GapMirrorCalculus.blowTime_pos
#print axioms GapMirrorCalculus.blows_up
#print axioms GapMirrorCalculus.mirror_sum
#print axioms GapMirrorCalculus.mirror_time
#print axioms GapMirrorBridge.cast_z
#print axioms GapMirrorBridge.cast_mirror
#print axioms GapMirrorBridge.cast_step
#print axioms GapMirrorBridge.denominator_factor
#print axioms GapMirrorBridge.real_step_at_time
#print axioms GapMirrorBridge.factor_at_blowTime
#print axioms GapMirrorBridge.before_iff
#print axioms GapMirrorBridge.same_motion_before_blowup
#print axioms GapMirrorBridge.rational_step_at_time
#print axioms GapMirrorBridge.clock_factor
#print axioms GapMirrorBridge.rational_step_at_clock
#print axioms GapMirrorBridge.real_step_solves_before
#print axioms GapMirrorBridge.both_in_future
#print axioms GapMirrorBridge.mirror_between
#print axioms GapMirrorBridge.lower_regular
#print axioms GapMirrorBridge.mirror_continues
#print axioms GapMirrorBridge.total_log_clock_identity
#print axioms GapMirrorBridge.factor_at_halfTime
#print axioms GapMirrorBridge.half_time_reaches_half
#print axioms GapMirrorBridge.halfTime_pos_iff
#print axioms GapMirrorBridge.halfTime_neg_iff
#print axioms GapMirrorBridge.halfTime_at_half
#print axioms GapMirrorBridge.halfTime_mirror
#print axioms RingGapBridge.sign_sq
#print axioms RingGapBridge.sign_mod
#print axioms RingGapBridge.sign_next
#print axioms RingGapBridge.flip_flip
#print axioms RingGapBridge.size_flip
#print axioms RingGapBridge.flipped_edge
#print axioms RingGapBridge.sum_shift
#print axioms RingGapBridge.cost_pair
#print axioms RingGapBridge.cost_flip
#print axioms RingGapBridge.normalized_pair
#print axioms RingGapBridge.gap_over_height
#print axioms RingGapBridge.z_height
#print axioms RingGapBridge.z_flip
#print axioms RingGapBridge.height_flip
#print axioms RingGapBridge.height_pos
#print axioms RingGapBridge.height_above_gap_iff
#print axioms RingGapBridge.size_scale
#print axioms RingGapBridge.cost_scale
#print axioms RingGapBridge.height_scale
#print axioms RingGapBridge.six_wave_sums
#print axioms RingGapBridge.six_wave_laplacian
#print axioms RingGapBridge.six_wave_height
#print axioms RingGapBridge.six_wave_heat_height
#print axioms RingGapBridge.six_wave_gap_rate
#print axioms FourDotGapBridge.shape_flip
#print axioms FourDotGapBridge.shape_heat
#print axioms FourDotGapBridge.pattern_flip
#print axioms FourDotGapBridge.pattern_heat
#print axioms FourDotGapBridge.amplitude_zero
#print axioms FourDotGapBridge.amplitude_neg
#print axioms FourDotGapBridge.amplitude_deriv
#print axioms FourDotGapBridge.flow_zero
#print axioms FourDotGapBridge.flow_flip
#print axioms FourDotGapBridge.continuous_heat
#print axioms FourDotGapBridge.readout_pattern
#print axioms FourDotGapBridge.readout_flow
#print axioms FourDotGapBridge.height_above_two
#print axioms FourDotGapBridge.height_reflection
#print axioms FourDotGapBridge.height_dilation
#print axioms FourDotGapBridge.motion
#print axioms FourDotGapBridge.readout_solves
#print axioms FourDotGapBridge.pole_time_pos
#print axioms FourDotGapBridge.amplitude_before_pole
#print axioms FourDotGapBridge.amplitude_at_pole
#print axioms FourDotGapBridge.pole_eq_blowTime
#print axioms FourDotGapBridge.preserves_motion_and_reflection
#print axioms FourDotGapBridge.both_readouts_solve
#print axioms FourDotGapBridge.readout_blows_up
#print axioms FourDotGapBridge.flipped_at_pole
#print axioms FourDotGapBridge.ring_regular_at_pole
#print axioms TwoWaveGapBridge.gap_pos
#print axioms TwoWaveGapBridge.flat_gap
#print axioms TwoWaveGapBridge.energy_zero
#print axioms TwoWaveGapBridge.energy_pos
#print axioms TwoWaveGapBridge.energy_deriv
#print axioms TwoWaveGapBridge.energy_factor
#print axioms TwoWaveGapBridge.ordinary_reduced
#print axioms TwoWaveGapBridge.signed_reduced
#print axioms TwoWaveGapBridge.ordinary_between
#print axioms TwoWaveGapBridge.signed_above_gap
#print axioms TwoWaveGapBridge.ordinary_z
#print axioms TwoWaveGapBridge.signed_z
#print axioms TwoWaveGapBridge.signed_is_mirror
#print axioms TwoWaveGapBridge.ordinary_motion
#print axioms TwoWaveGapBridge.signed_motion
#print axioms TwoWaveGapBridge.crossing_factor
#print axioms TwoWaveGapBridge.energies_equal_iff
#print axioms TwoWaveGapBridge.rough_larger_before
#print axioms TwoWaveGapBridge.pole_time_pos_iff
#print axioms TwoWaveGapBridge.pole_time_neg_iff
#print axioms TwoWaveGapBridge.equal_sizes_pole_zero
#print axioms TwoWaveGapBridge.pole_eq_blowTime
#print axioms TwoWaveGapBridge.ordinary_solves
#print axioms TwoWaveGapBridge.signed_solves_regular
#print axioms TwoWaveGapBridge.signed_solves_before
#print axioms TwoWaveGapBridge.signed_blows_up
#print axioms TwoWaveGapBridge.ordinary_at_pole
#print axioms TwoWaveGapBridge.no_future_pole
#print axioms TwoWaveGapBridge.future_pole_iff
#print axioms TwoWaveGapBridge.ordinary_fades
#print axioms TwoWaveGapBridge.pure_rough
#print axioms TwoWaveGapBridge.pure_smooth
#print axioms TwoWaveGapBridge.cost_ratio_map
#print axioms TwoWaveGapBridge.signed_ratio_map
#print axioms TwoWaveGapBridge.mirror_at_time
#print axioms TwoWaveGapBridge.cross_shift
#print axioms TwoWaveGapBridge.cost_eq_neg_dot_heat
#print axioms TwoWaveGapBridge.size_mix
#print axioms TwoWaveGapBridge.dot_mix
#print axioms TwoWaveGapBridge.heat_mix
#print axioms TwoWaveGapBridge.cost_mix
#print axioms TwoWaveGapBridge.coefficient_deriv
#print axioms TwoWaveGapBridge.coefficient_energy
#print axioms TwoWaveGapBridge.continuous_heat
#print axioms TwoWaveGapBridge.flow_size
#print axioms TwoWaveGapBridge.flow_cost
#print axioms TwoWaveGapBridge.ring_readout
#print axioms TwoWaveGapBridge.ring_motion
#print axioms TwoWaveGapBridge.ring_signed_mirror
#print axioms TwoWaveGapBridge.ring_regular
#print axioms TwoWaveGapBridge.ring_signed_event
#print axioms TwoWaveGapBridge.flat4_eigen
#print axioms TwoWaveGapBridge.rough4_eigen
#print axioms TwoWaveGapBridge.four_mode_data
#print axioms TwoWaveGapBridge.concrete_signed_event
#print axioms TwoWaveDiscreteGapBridge.factor_square
#print axioms TwoWaveDiscreteGapBridge.factor_pos
#print axioms TwoWaveDiscreteGapBridge.forward_multipliers
#print axioms TwoWaveDiscreteGapBridge.stable_multiplier
#print axioms TwoWaveDiscreteGapBridge.factor_gt_one
#print axioms TwoWaveDiscreteGapBridge.clock_pos
#print axioms TwoWaveDiscreteGapBridge.zero_step
#print axioms TwoWaveDiscreteGapBridge.clock_factor
#print axioms TwoWaveDiscreteGapBridge.sample_clock_factor
#print axioms TwoWaveDiscreteGapBridge.sample_energy_zero
#print axioms TwoWaveDiscreteGapBridge.sample_energy_pos
#print axioms TwoWaveDiscreteGapBridge.sample_energy_factor
#print axioms TwoWaveDiscreteGapBridge.ordinary_reduced
#print axioms TwoWaveDiscreteGapBridge.signed_reduced
#print axioms TwoWaveDiscreteGapBridge.ordinary_sample
#print axioms TwoWaveDiscreteGapBridge.signed_sample
#print axioms TwoWaveDiscreteGapBridge.ordinary_motion
#print axioms TwoWaveDiscreteGapBridge.signed_motion
#print axioms TwoWaveDiscreteGapBridge.ordinary_one_step
#print axioms TwoWaveDiscreteGapBridge.signed_one_step
#print axioms TwoWaveDiscreteGapBridge.sample_mirror
#print axioms TwoWaveDiscreteGapBridge.signed_denominator
#print axioms TwoWaveDiscreteGapBridge.pole_at_sample_iff
#print axioms TwoWaveDiscreteGapBridge.before_pole_iff
#print axioms TwoWaveDiscreteGapBridge.pole_clock_iff
#print axioms TwoWaveDiscreteGapBridge.before_index_iff
#print axioms TwoWaveDiscreteGapBridge.signed_regular_before
#print axioms TwoWaveDiscreteGapBridge.heat_step_mix
#print axioms TwoWaveDiscreteGapBridge.iterate_heat_mix
#print axioms TwoWaveDiscreteGapBridge.sample_coefficient_energy
#print axioms TwoWaveDiscreteGapBridge.iterate_size
#print axioms TwoWaveDiscreteGapBridge.iterate_cost
#print axioms TwoWaveDiscreteGapBridge.iterate_readout
#print axioms TwoWaveDiscreteGapBridge.iterate_motion
#print axioms TwoWaveDiscreteGapBridge.heat_step_readout
#print axioms TwoWaveDiscreteGapBridge.iterate_signed_mirror
#print axioms TwoWaveDiscreteGapBridge.killed_rough_mode
#print axioms TwoWaveDiscreteGapBridge.concrete_clock
#print axioms TwoWaveDiscreteGapBridge.concrete_hits_pole
#print axioms TwoWaveDiscreteGapBridge.concrete_skips_pole
#print axioms TwoWaveFlipBridge.orient_swap
#print axioms TwoWaveFlipBridge.orient_pos_neg
#print axioms TwoWaveFlipBridge.orient_neg_pos
#print axioms TwoWaveFlipBridge.orient_zero_iff
#print axioms TwoWaveFlipBridge.orient_ne_zero_iff
#print axioms TwoWaveFlipBridge.orient_positive_iff
#print axioms TwoWaveFlipBridge.orient_scale
#print axioms TwoWaveFlipBridge.orient_heat
#print axioms TwoWaveFlipBridge.height_zero
#print axioms TwoWaveFlipBridge.height_nonzero_iff
#print axioms TwoWaveFlipBridge.height_reflection
#print axioms TwoWaveFlipBridge.height_above_gap
#print axioms TwoWaveFlipBridge.height_dilation
#print axioms TwoWaveFlipBridge.height_motion
#print axioms TwoWaveFlipBridge.decay_before_pole
#print axioms TwoWaveFlipBridge.pole_eq_blowTime
#print axioms TwoWaveFlipBridge.finite_pair_iff
#print axioms TwoWaveFlipBridge.matching_rate_iff
#print axioms TwoWaveFlipBridge.linear_readout_iff
#print axioms TwoWaveFlipBridge.decay_deriv
#print axioms TwoWaveFlipBridge.height_deriv
#print axioms TwoWaveFlipBridge.solves_iff
#print axioms TwoWaveFlipBridge.linear_paired_iff
#print axioms TwoWaveFlipBridge.sign_prev
#print axioms TwoWaveFlipBridge.heat_flip
#print axioms TwoWaveFlipBridge.flipped_eigen
#print axioms TwoWaveFlipBridge.flip_reverse
#print axioms TwoWaveFlipBridge.paired_eigenvalues
#print axioms TwoWaveFlipBridge.dot_flip
#print axioms TwoWaveFlipBridge.modal_flip
#print axioms TwoWaveFlipBridge.amplitude_flip
#print axioms TwoWaveFlipBridge.readout_flip
#print axioms TwoWaveFlipBridge.modal_mix_left
#print axioms TwoWaveFlipBridge.modal_mix_right
#print axioms TwoWaveFlipBridge.amplitude_mix
#print axioms TwoWaveFlipBridge.readout_mix
#print axioms TwoWaveFlipBridge.active_iff
#print axioms TwoWaveFlipBridge.flip_mix
#print axioms TwoWaveFlipBridge.amplitude_flow
#print axioms TwoWaveFlipBridge.flow_readout
#print axioms TwoWaveFlipBridge.paired_motion_and_flip
#print axioms TwoWaveFlipBridge.signed_multiplier_positive_iff
#print axioms TwoWaveFlipBridge.orient_scaled_opposite
#print axioms TwoWaveFlipBridge.positive_step_scale_iff
#print axioms TwoWaveFlipBridge.step_factor_positive
#print axioms TwoWaveFlipBridge.step_clock_factor
#print axioms TwoWaveFlipBridge.step_factor_forward
#print axioms TwoWaveFlipBridge.step_clock_forward
#print axioms TwoWaveFlipBridge.iterate_clock_factor
#print axioms TwoWaveFlipBridge.product_power_factor
#print axioms TwoWaveFlipBridge.iterate_amplitude
#print axioms TwoWaveFlipBridge.iterate_readout_motion
#print axioms TwoWaveFlipBridge.iterate_flip_readout
#print axioms TwoWaveFlipBridge.discrete_mirror_before
#print axioms TwoWaveFlipBridge.height_positive_iff
#print axioms TwoWaveFlipBridge.positive_pair_iff
#print axioms TwoWaveFlipBridge.flat_rough_flip
#print axioms TwoWaveFlipBridge.concrete_readouts
#print axioms TwoWaveFlipBridge.concrete_both
#print axioms TwoWaveFlipBridge.concrete_step
#print axioms TwoWaveReadoutObstruction.diagonal_zero
#print axioms TwoWaveReadoutObstruction.meeting_time
#print axioms TwoWaveReadoutObstruction.zero_of_same_sign
#print axioms TwoWaveReadoutObstruction.zero_of_positive
#print axioms TwoWaveReadoutObstruction.zero_of_negative
#print axioms TwoWaveReadoutObstruction.proposed_statement
#print axioms TwoWaveReadoutObstruction.equal_rates_counterexample
#print axioms HypercubeIso.hammingDist_cons
#print axioms HypercubeIso.sum_cube_succ
#print axioms HypercubeIso.size_succ
#print axioms HypercubeIso.w_same
#print axioms HypercubeIso.w_cross
#print axioms HypercubeIso.sum_cross
#print axioms HypercubeIso.dir_succ
#print axioms HypercubeIso.common_le_true
#print axioms HypercubeIso.common_le_false
#print axioms HypercubeIso.dir_zero
#print axioms HypercubeIso.natlog_nonneg
#print axioms HypercubeIso.key
#print axioms HypercubeIso.edges_le
#print axioms RingDecay.gap_eq_four_sin_sq
#print axioms RingDecay.gap_pos
#print axioms RingDecay.fourier_heatStep
#print axioms RingDecay.sum_heatStep
#print axioms RingDecay.mean_heatStep
#print axioms RingDecay.energy_heatStep_le
#print axioms RingDecay.energy_heatStep_le_mean
#print axioms RingDecay.mean_iterate
#print axioms RingDecay.energy_iterate_le
#print axioms RingDecay.factor_lt_one
#print axioms RingDecay.energy_tendsto_zero
#print axioms RingDecay.iterate_tendsto_mean
#print axioms RingDecay.heatStep_wave
#print axioms RingDecay.energy_heatStep_wave
#print axioms HarperVertex.before_trans
#print axioms HarperVertex.before_total
#print axioms HarperVertex.init_eq_of_card_eq
#print axioms HarperVertex.isInit_initSeg
#print axioms HarperVertex.card_initSeg
#print axioms HarperVertex.nonMember_nbhd
#print axioms HarperVertex.member_nbhd
#print axioms HarperVertex.isInit_nbhd
#print axioms HarperVertex.card_squash
#print axioms HarperVertex.card_nbhd_squash_le
#print axioms HarperVertex.weight_squash_lt
#print axioms HarperVertex.eq_sdiff_of_squashedAll
#print axioms HarperVertex.exceptional_adj
#print axioms HarperVertex.squashedAll_classify
#print axioms HarperVertex.card_nbhd_le_of_squashedAll
#print axioms HarperVertex.harperAt
#print axioms HarperVertex.harper
#print axioms HarperVertex.harper_cube
#print axioms HarperVertex.card_ball
#print axioms HarperVertex.harper_ball
#print axioms HarperVertex.harper_ball_choose

#print axioms PolygonIso.plancherel
#print axioms PolygonIso.cfourier_shift
#print axioms PolygonIso.cfourier_step
#print axioms PolygonIso.e_im
#print axioms PolygonIso.normSq_e
#print axioms PolygonIso.tan_bound
#print axioms PolygonIso.area2_fourier
#print axioms PolygonIso.sides_fourier
#print axioms PolygonIso.polygon_isoperimetric
#print axioms PolygonIso.polygon_sharp
#print axioms CubeCheeger.hammingDist_cons
#print axioms CubeCheeger.sum_cube_succ
#print axioms CubeCheeger.adj_comm
#print axioms CubeCheeger.adj_nonneg
#print axioms CubeCheeger.adj_cons
#print axioms CubeCheeger.energy_nonneg
#print axioms CubeCheeger.card_cube
#print axioms CubeCheeger.energy_succ
#print axioms CubeCheeger.spread_succ
#print axioms CubeCheeger.cross_le
#print axioms CubeCheeger.gap
#print axioms CubeCheeger.ind_sq_diff
#print axioms CubeCheeger.sum_ind
#print axioms CubeCheeger.energy_ind
#print axioms CubeCheeger.spread_ind
#print axioms CubeCheeger.cheeger
#print axioms CubeCheeger.half_exact
#print axioms Bridges.cycle_gap_two
#print axioms Bridges.spread_of_mean_zero
#print axioms Bridges.cube_poincare
#print axioms Bridges.cfourier_ofReal
#print axioms Bridges.parseval_real_of_plancherel
#print axioms CartesianGraphProduct.energy_cartesian
#print axioms CartesianGraphProduct.cartesian_gap
#print axioms CartesianGraphProduct.cartesian_gap_iff
#print axioms CartesianGraphProduct.cartesian_gap_sharp
#print axioms CartesianGraphProduct.energy_eq_lapMatrix
#print axioms CartesianGraphProduct.simpleWeight_boxProd
#print axioms CartesianGraphProduct.boxProd_gap
#print axioms CartesianGraphProduct.boxProd_gap_sharp
#print axioms CartesianGraphProduct.simpleWeight_boxPi
#print axioms CartesianGraphProduct.piWeight_split
#print axioms CartesianGraphProduct.pi_gap_of_isEmpty
#print axioms CartesianGraphProduct.pi_no_sharpGap_of_isEmpty
#print axioms CartesianGraphProduct.pi_gap_iff
#print axioms CartesianGraphProduct.pi_gap
#print axioms CartesianGraphProduct.pi_gap_sharp
#print axioms CartesianGraphProduct.boxPi_gap_iff
#print axioms CartesianGraphProduct.boxPi_gap
#print axioms CartesianGraphProduct.boxPi_gap_sharp
#print axioms RingGrid.sum_sq_add_of_sum_zero
#print axioms RingGrid.row_sub_mean
#print axioms RingGrid.sum_rowMean
#print axioms RingGrid.sum_sq_split
#print axioms RingGrid.first_steps_split
#print axioms RingGrid.second_steps_ge
#print axioms RingGrid.ringWeight_energy
#print axioms RingGrid.energy_eq_cartesian
#print axioms RingGrid.grid_gap
#print axioms RingGrid.ring_wave
#print axioms RingGrid.rowWave_sharp
#print axioms RingGrid.colWave_sharp
#print axioms RingGrid.grid_gap_sharp
#print axioms RingGrid.ring_isSharpGap
#print axioms RingGrid.torus_gap_sharp
#print axioms RingGrid.sum_shift_fst
#print axioms RingGrid.sum_shift_snd
#print axioms RingGrid.sum_lap
#print axioms RingGrid.sum_heatStep
#print axioms RingGrid.mean_heatStep
#print axioms RingGrid.sum_mul_lap
#print axioms RingGrid.sum_lap_sq_le
#print axioms RingGrid.sum_sq_heatStep
#print axioms RingGrid.sum_sq_heatStep_le
#print axioms RingGrid.heatStep_decay
#print axioms RingGrid.heatStep_decay_eighth
#print axioms RingGrid.heatStep_sub_const
#print axioms RingGrid.sum_sub_mean
#print axioms RingGrid.heatStep_decay_mean
#print axioms RingGrid.mean_iterate
#print axioms RingGrid.factor_nonneg
#print axioms RingGrid.iterate_decay
#print axioms RingGrid.factor_lt_one
#print axioms RingGrid.energy_tendsto_zero
#print axioms RingGrid.iterate_tendsto_mean

-- WallPush
#print axioms HugWallPush.shifted_flux_sum
#print axioms HugWallPush.wall_total_zero
#print axioms HugWallPush.wall_energy
#print axioms HugWallPush.wallHeat_nonneg
#print axioms HugWallPush.wall_only_takes
#print axioms HugWallPush.grid_total_zero
#print axioms HugWallPush.grid_energy
#print axioms HugWallPush.wall_keeps_total
#print axioms HugWallPush.count_closes
#print axioms HugWallPush.push_changes_total
#print axioms HugWallPush.push_moves_one_way
#print axioms HugWallPush.balanced_push_keeps_total
#print axioms HugWallPush.push_moves_box
#print axioms HugWallPush.lin_deriv
#print axioms HugWallPush.sideA_deriv
#print axioms HugWallPush.sideB_deriv
#print axioms HugWallPush.average_fixed
#print axioms HugWallPush.difference_fades
#print axioms HugWallPush.thicker_balances_faster
#print axioms HugWallPush.exp_double
#print axioms HugWallPush.two_sides_count_closes
#print axioms HugWallPush.twoSideHeat_deriv
#print axioms HugWallPush.twoSideHeat_nonneg
#print axioms HugWallPush.half_one_add_tanh_le
#print axioms HugWallPush.dip_floor_normalized
#print axioms HugWallPush.dip_floor
#print axioms HugWallPush.total_viscosity_never_negative
#print axioms HugWallPush.breath_telescopes
#print axioms HugWallPush.delayed_baseline_record
#print axioms HugWallPush.delayed_baseline_bounded
#print axioms HugWallPush.frozen_baseline_fills
#print axioms HugWallPush.freeze_step_counts
#print axioms HugWallPush.clocks_meet_at_ticks
#print axioms HugWallPush.shares_whole
#print axioms HugWallPush.balance_between
#print axioms HugWallPush.gap_split
#print axioms HugWallPush.freeze_keeps_total
#print axioms HugWallPush.freeze_gives_off
#print axioms HugWallPush.freeze_gives_off_nonneg
#print axioms HugWallPush.clayHeat_nonneg
#print axioms HugWallPush.clay_energy
#print axioms HugWallPush.wall_clay_energy
#print axioms HugWallPush.clay_push_total
#print axioms HugWallPush.uniform_box_rate
#print axioms HugWallPush.uniform_box_toward_settling
#print axioms HugWallPush.clay_brakes_box
#print axioms HugWallPush.broken_clay_no_brake
#print axioms HugWallPush.boxSpeed_deriv
#print axioms HugWallPush.boxSpeed_settles
#print axioms HugWallPush.integrity_stays
#print axioms HugWallPush.integrity_yields
#print axioms HugWallPush.integrity_recovers

-- Harper (stage 1; namespace Harper, so it sits beside HarperSquash's HarperVertex)
#print axioms Harper.mem_nbhd
#print axioms Harper.subset_nbhd
#print axioms Harper.key_injective
#print axioms Harper.rank_lt_rank
#print axioms Harper.rank_injective
#print axioms Harper.rank_lt_card
#print axioms Harper.image_rank
#print axioms Harper.card_seg
#print axioms Harper.card_seg_le
#print axioms Harper.seg_mono
#print axioms Harper.card_seg_union
#print axioms Harper.sum_split
#print axioms Harper.card_split
#print axioms Harper.hammingDist_insertNth
#print axioms Harper.slice_nbhd
#print axioms Harper.slice_squash
#print axioms Harper.card_squash
#print axioms Harper.squash_nbhd_le

-- Unify
#print axioms Unify.mode_compare
#print axioms Unify.ring_mode
#print axioms Unify.wirtinger_by_modes
#print axioms Unify.polygon_mode
#print axioms Unify.polygon_by_modes
#print axioms Unify.ind_sq_diff
#print axioms Unify.sum_ind
#print axioms Unify.energy_ind
#print axioms Unify.spread_ind
#print axioms Unify.spread_of_mean_zero
#print axioms Unify.patch_from_gap
#print axioms Unify.cube_cheeger_by_gap
#print axioms Unify.ringW_comm
#print axioms Unify.ring_energy
#print axioms Unify.ring_gap
#print axioms Unify.ring_patch

-- Extended binary Golay code
#print axioms GolayMatrixDistance.golay_self_orthogonal
#print axioms GolayMatrixDistance.golay_doubly_even_and_d_min_8
#print axioms GolayMatrixDistance.golay_sharp_weight_8
#print axioms GolayMatrixDistance.golay_min_distance_bound
#print axioms GolayMatrixDistance.golay_weight_distribution
#print axioms HypercubeEdgeOptimal.ones
#print axioms HypercubeEdgeOptimal.h
#print axioms HypercubeEdgeOptimal.ones_double
#print axioms HypercubeEdgeOptimal.ones_double_add_one
#print axioms HypercubeEdgeOptimal.h_zero
#print axioms HypercubeEdgeOptimal.h_one
#print axioms HypercubeEdgeOptimal.h_succ
#print axioms HypercubeEdgeOptimal.h_double
#print axioms HypercubeEdgeOptimal.h_double_add_one
#print axioms HypercubeEdgeOptimal.h_split
#print axioms HypercubeEdgeOptimal.binary_sum
#print axioms HypercubeEdgeOptimal.val
#print axioms HypercubeEdgeOptimal.val_cons
#print axioms HypercubeEdgeOptimal.val_eq_sum
#print axioms HypercubeEdgeOptimal.bin
#print axioms HypercubeEdgeOptimal.bin_true
#print axioms HypercubeEdgeOptimal.bin_false
#print axioms HypercubeEdgeOptimal.common_bin
#print axioms HypercubeEdgeOptimal.size_le
#print axioms HypercubeEdgeOptimal.size_bin
#print axioms HypercubeEdgeOptimal.size_bin_of_le
#print axioms HypercubeEdgeOptimal.dir_bin
#print axioms HypercubeEdgeOptimal.dir_le_two_mul_h
#print axioms HypercubeEdgeOptimal.dir_le_dir_bin
#print axioms HypercubeEdgeOptimal.max_dir_eq

-- E8 plumbing matrix
#print axioms E8PlumbingBridge.A4_isSymm
#print axioms E8PlumbingBridge.A4_det
#print axioms E8PlumbingBridge.E8_isSymm
#print axioms E8PlumbingBridge.E8_det
#print axioms E8PlumbingBridge.E8_trace
#print axioms E8PlumbingBridge.card_spinor_roots
#print axioms E8PlumbingBridge.card_integer_roots
#print axioms E8PlumbingBridge.total_E8_roots

#print axioms E8Tab30Bridge.simpleRoots_sq_length
#print axioms E8Tab30Bridge.gram_entry
#print axioms E8Tab30Bridge.gram_matrix
#print axioms E8Tab30Bridge.E8Q_det
#print axioms E8Tab30Bridge.det_G

-- Extended Hamming [8,4,4] code of playground tab 30
#print axioms HammingCode.encode_injective
#print axioms HammingCode.card_code
#print axioms HammingCode.mem_code_iff
#print axioms HammingCode.weight_distribution
#print axioms HammingCode.doubly_even
#print axioms HammingCode.min_distance
#print axioms HammingCode.min_distance_sharp
#print axioms HammingCode.G_mul_transpose
#print axioms HammingCode.self_orthogonal
#print axioms HammingCode.code_eq_dual
#print axioms HammingCode.tabSpinor_sqLength
#print axioms HammingCode.tabSpinor_injective
#print axioms HammingCode.card_allTabSpinors
#print axioms HammingCode.tabSpinor_evenParity
#print axioms HammingCode.allTabSpinors_eq_evenSpinors
#print axioms HammingCode.card_allTabSpinors_eq_spinor_roots

-- Stick placement and the cost of one or two plumbings
#print axioms PlumbingStick.rowStick_seven_four
#print axioms PlumbingStick.stick_det
#print axioms PlumbingStick.stick_det_eq_one_iff
#print axioms PlumbingStick.flipRow_flipRow
#print axioms PlumbingStick.stick_mirror
#print axioms PlumbingStick.stick_mirror_det
#print axioms PlumbingStick.nine_det
#print axioms PlumbingStick.ten_det
#print axioms PlumbingStick.cost_as_joints
#print axioms PlumbingStick.cost_even
#print axioms PlumbingStick.cost_pos
#print axioms PlumbingStick.cost_ge_two
#print axioms PlumbingStick.cost_single
#print axioms PlumbingStick.two_separate_pos
#print axioms PlumbingStick.one_joint_breaks

-- Shares, determinants and cost for a row with one stick
#print axioms PlumbingHelp.total_spare
#print axioms PlumbingHelp.stickCost_as_joints
#print axioms PlumbingHelp.stickCost_seven_four
#print axioms PlumbingHelp.rowStick_det
#print axioms PlumbingHelp.margin_eq_help
#print axioms PlumbingHelp.margin_pos_iff_help
#print axioms PlumbingHelp.margin_zero_iff_help
#print axioms PlumbingHelp.e8_help
#print axioms PlumbingHelp.free_ride_middle
#print axioms PlumbingHelp.free_ride_nine
#print axioms PlumbingHelp.ten_breaks
#print axioms PlumbingHelp.seven_never_free_iff

-- E8 cost mirror
#print axioms E8CostMirror.cost_pair

-- Golay to Leech counting bridge
#print axioms GolayLeechBridge.golay_total_codewords
#print axioms GolayLeechBridge.golay_octad_count
#print axioms GolayLeechBridge.leech_shape3_eq
#print axioms GolayLeechBridge.leech_shape1_eq
#print axioms GolayLeechBridge.leech_shape2_eq
#print axioms GolayLeechBridge.leech_kissing_decomposition
#print axioms GolayLeechBridge.E8_and_Leech_summary
#print axioms GolayLeechBridge.golayWeightCount_eq_code
#print axioms GolayLeechBridge.leech_kissing_from_code

-- Leech lattice from the Golay code: definition and smallest length
#print axioms LeechLattice.natBit_eq
#print axioms LeechLattice.bitAt_eq_testBit
#print axioms LeechLattice.bitAt_xor
#print axioms LeechLattice.popcount_foldl
#print axioms LeechLattice.popcount24_eq_card_bitAt
#print axioms LeechLattice.popcount24_eq_card
#print axioms LeechLattice.encodeNat_eq_foldl
#print axioms LeechLattice.u32_xor_left_comm
#print axioms LeechLattice.foldl_encodeStep_xor
#print axioms LeechLattice.encodeNat_xor
#print axioms LeechLattice.encodeNat_zero
#print axioms LeechLattice.word_encodeNat_4095
#print axioms LeechLattice.word_zero
#print axioms LeechLattice.isGolayWord_false
#print axioms LeechLattice.isGolayWord_true
#print axioms LeechLattice.isGolayWord_xor
#print axioms LeechLattice.isGolayWord_not
#print axioms LeechLattice.card_true_of_isGolayWord
#print axioms LeechLattice.golay_weight_mod_four
#print axioms LeechLattice.golay_weight_ge_eight
#print axioms LeechLattice.inLeech_iff
#print axioms LeechLattice.sum_add'
#print axioms LeechLattice.sum_neg'
#print axioms LeechLattice.evenLeech_add
#print axioms LeechLattice.oddLeech_add
#print axioms LeechLattice.odd_even_add
#print axioms LeechLattice.evenLeech_neg
#print axioms LeechLattice.oddLeech_neg
#print axioms LeechLattice.leechLattice
#print axioms LeechLattice.mem_leechLattice
#print axioms LeechLattice.oddLeech_norm_ge
#print axioms LeechLattice.evenLeech_norm_ge_of_two
#print axioms LeechLattice.evenLeech_norm_ge_of_four
#print axioms LeechLattice.leech_norm_ge_32
#print axioms LeechLattice.vecFourFour_mem
#print axioms LeechLattice.vecFourFour_norm
#print axioms LeechLattice.vecOctad_mem
#print axioms LeechLattice.vecOctad_norm
#print axioms LeechLattice.vecThree_mem
#print axioms LeechLattice.vecThree_norm
#print axioms LeechLattice.vecFour_not_mem
#print axioms LeechLattice.vecOnes_not_mem
#print axioms LeechLattice.leech_min_norm

-- Leech shortest-vector classification and counts (private helpers are included transitively)
#print axioms LeechMinimal.sum_of_signed_support
#print axioms LeechMinimal.norm_of_signed_support
#print axioms LeechMinimal.coordinate_sq_le
#print axioms LeechMinimal.four_classification
#print axioms LeechMinimal.octad_classification
#print axioms LeechMinimal.odd_classification
#print axioms LeechMinimal.minimal_classification
#print axioms LeechMinimal.four_mem_norm
#print axioms LeechMinimal.octad_mem_norm
#print axioms LeechMinimal.oddVector_residue
#print axioms LeechMinimal.oddVector_norm
#print axioms LeechMinimal.oddVector_sum
#print axioms LeechMinimal.oddVector_mem
#print axioms LeechMinimal.odd_mem_norm
#print axioms LeechMinimal.minimal_iff
#print axioms LeechCodeCounts.word_encode_injective
#print axioms LeechCodeCounts.encodeWord_bijective
#print axioms LeechCodeCounts.card_codeword
#print axioms LeechCodeCounts.blockCounts_eight
#print axioms LeechCodeCounts.weightCounts_eight
#print axioms LeechCodeCounts.weightCounts_eight_sum
#print axioms LeechCodeCounts.card_octad_eq_weightCounts
#print axioms LeechCodeCounts.card_octad
#print axioms LeechSignVectors.signedVector_values
#print axioms LeechSignVectors.signedVector_support
#print axioms LeechSignVectors.signedVector_recover
#print axioms LeechSignVectors.signedVector_injective
#print axioms LeechSignVectors.signedVector_negative_card
#print axioms LeechSignVectors.evenSigns_precomp
#print axioms LeechSignVectors.card_evenSigns_eight
#print axioms LeechMinimal.fourMap_bijective
#print axioms LeechMinimal.card_four_params
#print axioms LeechMinimal.card_four
#print axioms LeechMinimal.oddVector_injective
#print axioms LeechMinimal.oddMap_bijective
#print axioms LeechMinimal.card_odd
#print axioms LeechMinimal.signed_two_residue
#print axioms LeechMinimal.octad_support
#print axioms LeechMinimal.octadMap_bijective
#print axioms LeechMinimal.card_octad_params
#print axioms LeechMinimal.card_octad_vectors
#print axioms LeechMinimal.four_octad_disjoint
#print axioms LeechMinimal.oddShape_parity
#print axioms LeechMinimal.four_odd_disjoint
#print axioms LeechMinimal.octad_odd_disjoint
#print axioms LeechMinimal.familyMap_bijective
#print axioms LeechMinimal.leech_kissing_number
#print axioms LeechMinimal.card_minimal_eq_code_formula
#print axioms LeechMinimal.shortest_iff_norm32
#print axioms LeechMinimal.card_shortest_vectors

-- Playground Golay correspondence and transfer of the existing Leech results
#print axioms PlaygroundGolay.quadraticResidues_eq
#print axioms PlaygroundGolay.computedBasis_eq
#print axioms PlaygroundGolay.toPlay_toLean
#print axioms PlaygroundGolay.toLean_toPlay
#print axioms PlaygroundGolay.isPlayWord_iff
#print axioms PlaygroundGolay.word_xor
#print axioms PlaygroundGolay.encodeWith_xor
#print axioms PlaygroundGolay.encodeWith_zero
#print axioms PlaygroundGolay.isPlayWord_false
#print axioms PlaygroundGolay.isPlayWord_xor
#print axioms PlaygroundGolay.forward_row
#print axioms PlaygroundGolay.reverse_row
#print axioms PlaygroundGolay.encodeWith_property
#print axioms PlaygroundGolay.play_toLean
#print axioms PlaygroundGolay.lean_toPlay
#print axioms PlaygroundGolay.code_correspondence
#print axioms PlaygroundGolay.weight_toLean
#print axioms PlaygroundGolay.card_play_code
#print axioms PlaygroundLeech.sum_toLean
#print axioms PlaygroundLeech.norm_toLean
#print axioms PlaygroundLeech.residue_toLean
#print axioms PlaygroundLeech.lattice_correspondence
#print axioms PlaygroundLeech.toLean_ne_zero
#print axioms PlaygroundLeech.play_norm_ge_32
#print axioms PlaygroundLeech.shortest_correspondence
#print axioms PlaygroundLeech.play_shortest_iff_norm32
#print axioms PlaygroundLeech.play_minimal_iff
#print axioms PlaygroundLeech.card_play_shortest_vectors

-- Leech lattice basis, determinant and unimodularity
#print axioms LeechBasis.leechBasis_zero_odd
#print axioms LeechBasis.leechBasis_even_facts
#print axioms LeechBasis.leechBasis_mem
#print axioms LeechBasis.basisSpan_le
#print axioms LeechBasis.mem_basisSpan_of_coeffs
#print axioms LeechBasis.twoRow_coeffs
#print axioms LeechBasis.fourDiff_coeffs
#print axioms LeechBasis.twoRow_mem
#print axioms LeechBasis.fourDiff_mem
#print axioms LeechBasis.eightLast_mem
#print axioms LeechBasis.fourDiff_eight_apply
#print axioms LeechBasis.mem_span_of_four
#print axioms LeechBasis.encodeNat_mod_check
#print axioms LeechBasis.encodeNat_mod_4096
#print axioms LeechBasis.golay_eq_false_of_first12
#print axioms LeechBasis.twoRow_apply_low
#print axioms LeechBasis.mem_span_of_even
#print axioms LeechBasis.closure_leechBasis
#print axioms LeechBasis.leechBasis_upper
#print axioms LeechBasis.basisMatrix_upper
#print axioms LeechBasis.leechBasis_diag_prod
#print axioms LeechBasis.basisMatrix_det
#print axioms LeechBasis.leechBasis_linearIndependent
#print axioms LeechBasis.gram_dvd_eight
#print axioms LeechBasis.gram_diag_dvd_sixteen
#print axioms LeechBasis.basisMatrix_mul_transpose
#print axioms LeechBasis.leech_unimodular
#print axioms LeechBasis.leech_inner_dvd_eight
#print axioms LeechBasis.leech_norm_dvd_sixteen

-- Three E8 blocks and their 4096 distinct glue cosets
#print axioms LeechThreeE8.coordinate_bijective
#print axioms LeechThreeE8.block_norm
#print axioms LeechThreeE8.base_blocks
#print axioms LeechThreeE8.e8_gram
#print axioms LeechThreeE8.base_gram
#print axioms LeechThreeE8.combination_mem
#print axioms LeechThreeE8.base_in_leech_check
#print axioms LeechThreeE8.glue_in_leech_check
#print axioms LeechThreeE8.leech_in_glued_check
#print axioms LeechThreeE8.twice_glue_check
#print axioms LeechThreeE8.base_mem
#print axioms LeechThreeE8.glue_mem
#print axioms LeechThreeE8.glued_eq_leech
#print axioms LeechThreeE8.twice_glue_mem
#print axioms LeechThreeE8.glued_norm_ge_32
#print axioms LeechThreeE8.playground_correspondence
#print axioms LeechThreeE8.glued_basis_and_volume
#print axioms LeechThreeE8.glued_kissing_number
#print axioms LeechThreeE8.glued_even
#print axioms LeechThreeE8.readout_base_check
#print axioms LeechThreeE8.readout_glue_check
#print axioms LeechThreeE8.readout_base_zero
#print axioms LeechThreeE8.readout_offset
#print axioms LeechThreeE8.offset_zero
#print axioms LeechThreeE8.offset_mem_glued
#print axioms LeechThreeE8.twice_offset_mem
#print axioms LeechThreeE8.offset_add_carry
#print axioms LeechThreeE8.base_le_glued
#print axioms LeechThreeE8.coset_eq_glued
#print axioms LeechThreeE8.offset_cosets_distinct
#print axioms LeechThreeE8.leech_unique_glue
#print axioms LeechThreeE8.glue_label_count

-- Symmetry foundations, Golay sign changes and the standard frame stabilizer
#print axioms LeechSymmetry.normSq_add
#print axioms LeechSymmetry.normSq_neg
#print axioms LeechSymmetry.normSq_sub
#print axioms LeechSymmetry.normSq_two_smul
#print axioms LeechSymmetry.map_norm
#print axioms LeechSymmetry.map_dot
#print axioms LeechSymmetry.basis_norm32
#print axioms LeechSymmetry.shortest_span
#print axioms LeechSymmetry.axis_mem
#print axioms LeechSymmetry.axis_norm
#print axioms LeechSymmetry.dot_axis
#print axioms LeechSymmetry.axes_sameModTwo
#print axioms LeechSymmetry.norm64_sameModTwo_orthogonal
#print axioms LeechSymmetry.sameModTwo_trans
#print axioms LeechSymmetry.standard_class
#print axioms LeechSymmetry.map_sameModTwo
#print axioms LeechSymmetry.fixes_axis_preserves_frame
#print axioms LeechSymmetry.shortestAction_injective
#print axioms LeechSymmetry.aut_finite
#print axioms LeechSymmetry.dot_add_left
#print axioms LeechSymmetry.mem_autGroup_iff
#print axioms LeechSymmetry.centralNegation_sq
#print axioms LeechSymmetry.centralNegation_commutes
#print axioms LeechSymmetry.centralNegation_ne_one
#print axioms LeechSymmetry.axis_neg_sameModTwo
#print axioms LeechSymmetry.standard_class_iff
#print axioms LeechSymmetry.frameVector_injective
#print axioms LeechSymmetry.frameVector_surjective
#print axioms LeechSymmetry.card_standardFrame
#print axioms LeechSymmetry.twiceWord_mem
#print axioms LeechSymmetry.signFlip_involutive
#print axioms LeechSymmetry.signFlip_norm
#print axioms LeechSymmetry.signFlip_add
#print axioms LeechSymmetry.selected_sum_dvd_four
#print axioms LeechSymmetry.signFlip_sum_mod_eight
#print axioms LeechSymmetry.signFlip_mem
#print axioms LeechSymmetry.signAut_injective
#print axioms LeechSymmetry.signAut_sq
#print axioms LeechSymmetry.signAut_xor
#print axioms LeechSymmetry.card_signSubgroup
#print axioms LeechSymmetry.permute_sum
#print axioms LeechSymmetry.permute_norm
#print axioms LeechSymmetry.permute_mem
#print axioms LeechSymmetry.codePermutation_symm
#print axioms LeechSymmetry.frame_signed_coordinates
#print axioms LeechSymmetry.residue_isCode
#print axioms LeechSymmetry.signed_coordinates_code
#print axioms LeechSymmetry.signed_coordinates_signs
#print axioms LeechSymmetry.frame_symmetry_factors
#print axioms LeechSymmetry.signedPermutation_preserves_frame
#print axioms LeechSymmetry.frame_stabilizer_iff
#print axioms LeechSymmetry.eq_top_of_norm64_transitive

#print axioms GolayMathieu.block_weight
#print axioms GolayMathieu.block_golay
#print axioms GolayMathieu.weight_relabel
#print axioms GolayMathieu.xor_weight
#print axioms GolayMathieu.octad_unique
#print axioms GolayMathieu.block_fixed
#print axioms GolayMathieu.fixed_base
#print axioms GolayMathieu.allowed_image
#print axioms GolayMathieu.pointMap_injective
#print axioms GolayMathieu.rep_rows
#print axioms GolayMathieu.perm_of_forward
#print axioms GolayMathieu.rep_code
#print axioms GolayMathieu.level_zero_iff
#print axioms GolayMathieu.rep_hits
#print axioms GolayMathieu.rep_prefix
#print axioms GolayMathieu.sectionAt_hits
#print axioms GolayMathieu.image_assemble
#print axioms GolayMathieu.image_card
#print axioms GolayMathieu.card_step
#print axioms GolayMathieu.card_last
#print axioms GolayMathieu.card_mathieu
#print axioms GolayMathieu.generation_step
#print axioms GolayMathieu.generators_complete
#print axioms LeechSextet.symmetric
#print axioms LeechSextet.square
#print axioms LeechSextet.numer_twice
#print axioms LeechSextet.numer_norm
#print axioms LeechSextet.mem_of_check
#print axioms LeechSextet.basis_image
#print axioms LeechSextet.integral_image
#print axioms LeechSextet.move_mem_double
#print axioms LeechSextet.move_add
#print axioms LeechSextet.move_norm
#print axioms LeechSextet.move_square
#print axioms LeechSextet.moves_frame

-- Gap-wave forcing, single-mode decay and the forecast tail
#print axioms GapWaveTail.lap_stream
#print axioms GapWaveTail.carry_two_waves
#print axioms GapWaveTail.carry_parallel
#print axioms GapWaveTail.carry_equal_length
#print axioms GapWaveTail.carry_single
#print axioms GapWaveTail.carry_feeds
#print axioms GapWaveTail.feed_eq_zero_iff
#print axioms GapWaveTail.feed_tested
#print axioms GapWaveTail.feed_tested_eq_zero_iff
#print axioms GapWaveTail.feed_tested_mirror
#print axioms GapWaveTail.box_gap
#print axioms GapWaveTail.box_gap_attained
#print axioms GapWaveTail.ring_gap_tends_to_box_gap
#print axioms GapWaveTail.lone_solves
#print axioms GapWaveTail.gap_wave_fades
#print axioms GapWaveTail.broad_zero
#print axioms GapWaveTail.broad_solves
#print axioms GapWaveTail.broad_no_feed
#print axioms GapWaveTail.broad_mirror
#print axioms GapWaveTail.peakTime_pos
#print axioms GapWaveTail.broad_peak
#print axioms GapWaveTail.broad_tail
#print axioms GapWaveTail.forecast_straight
#print axioms GapWaveTail.forecast_mirror
#print axioms GapWaveTail.forecast_peak
#print axioms GapWaveTail.forecast_tail

#print axioms ConwayMoves.four_transitive
#print axioms ConwayMoves.four_signs
#print axioms ConwayMoves.sign_mem
#print axioms ConwayMoves.perm_mem
#print axioms ConwayMoves.sextet_mem
#print axioms ConwayMoves.reaches_refl
#print axioms ConwayMoves.reaches_trans
#print axioms ConwayMoves.reaches_symm
#print axioms ConwayMoves.reaches_norm
#print axioms ConwayMoves.arrange_four
#print axioms ConwayMoves.first_numer
#print axioms ConwayMoves.first_norm_move
#print axioms ConwayMoves.four_sum_bound
#print axioms ConwayMoves.norm64_transitive
#print axioms ConwayMoves.generators_span_aut
#print axioms ConwayIncidence.move_indices
#print axioms ConwayGenerators.listed_generate
#print axioms ConwayIncidence.indicator_sum
#print axioms ConwayIncidence.tally_even
#print axioms ConwayIncidence.tally_odd
#print axioms ConwayIncidence.column
#print axioms ConwayIncidence.column_total
#print axioms ConwayIncidence.row_total
#print axioms ConwayIncidence.card_neighbors
#print axioms ConwayPairs.root_dot
#print axioms ConwayPairs.roots_sum
#print axioms ConwayPairs.roots_sub
#print axioms ConwayPairs.coord_bound
#print axioms ConwayPairs.four_of_first
#print axioms ConwayPairs.root_unique
#print axioms ConwayPairs.pair_transitive
#print axioms ConwayPairs.shortest_has_partner
#print axioms ConwayPairs.shortest_transitive
#print axioms ConwayPairs.fixes_pair_iff
#print axioms ConwayStabilizer.mask_bits
#print axioms ConwayStabilizer.card_signs
#print axioms ConwayStabilizer.card_reorderings_fix_two
#print axioms ConwayStabilizer.monomial_axis
#print axioms ConwayStabilizer.monomial_fixes_iff
#print axioms ConwayStabilizer.assemble_bijective
#print axioms ConwayStabilizer.card_fix_axes
#print axioms ConwayOrder.card_partner
#print axioms ConwayOrder.card_pairs
#print axioms ConwayOrder.card_aut

#print axioms LeechCoordinateFrames.frame_transitive
#print axioms LeechCoordinateFrames.card_frame_stabilizer
#print axioms LeechCoordinateFrames.card_coordinate_frames
#print axioms LeechCoordinateFrames.existsUnique_frame_of_norm64
#print axioms LeechCoordinateFrames.card_norm64_vectors

#print axioms LeechCodeCounts.card_dodecad
#print axioms LeechNorm48Count.card_picks
#print axioms LeechNorm48Count.odd_choices
#print axioms LeechNorm48Count.even_choices
#print axioms LeechNorm48.card_norm48_vectors

#print axioms LeechNorm48.existsUnique_opposite_pair
#print axioms LeechNorm48.card_members_of_opposite_pair
#print axioms LeechNorm48.card_norm48_opposite_pairs

#print axioms LeechOppositePairs.existsUnique_opposite_pair
#print axioms LeechOppositePairs.card_members_of_opposite_pair
#print axioms LeechOppositePairs.card_opposite_pairs
#print axioms LeechOppositePairs.card_norm32_opposite_pairs
#print axioms LeechOppositePairs.card_norm64_opposite_pairs

#print axioms LeechNorm48Count.tally_eval
#print axioms LeechNorm48Count.odd_tally
#print axioms LeechShellCoordinates.card_vectors_from_choices
#print axioms LeechNorm80Count.odd_choices
#print axioms LeechNorm80Count.even_choices
#print axioms LeechNorm80.coordinate_bounds
#print axioms LeechNorm80.card_weight_sixteen
#print axioms LeechNorm80.card_norm80_vectors
#print axioms LeechNorm80.card_norm80_opposite_pairs

#print axioms LeechLayers.card_perpendicular
#print axioms LeechLayers.no_dot_twenty_four

#print axioms LightBounceAndCapture.AllowedShare.lt_one
#print axioms LightBounceAndCapture.reflected_le
#print axioms LightBounceAndCapture.reflected_le_cap
#print axioms LightBounceAndCapture.absorbed_ge
#print axioms LightBounceAndCapture.incoming_eq_absorbed_add_reflected
#print axioms LightBounceAndCapture.remainder_eq
#print axioms LightBounceAndCapture.remainder_le
#print axioms LightBounceAndCapture.remainder_tendsto_zero
#print axioms LightBounceAndCapture.absorbed_sum_add_remainder
#print axioms LightBounceAndCapture.absorbed_sum_tendsto
#print axioms LightBounceAndCapture.bounce_le
#print axioms LightBounceAndCapture.bounce_tendsto_zero
#print axioms LightBounceAndCapture.superBlackChannel_le
#print axioms LightBounceAndCapture.neighbor_share_bounds
#print axioms LightBounceAndCapture.once_in_never_out
#print axioms LightBounceAndCapture.once_in_never_out_frames
#print axioms LightBounceAndCapture.GrainMove.kind_eq
#print axioms LightBounceAndCapture.GrainMove.y_le
#print axioms LightBounceAndCapture.superBlackRegion_mapsTo
#print axioms LightBounceAndCapture.super_black_grain_stays_at_or_below
#print axioms LightBounceAndCapture.super_black_grain_stays_at_or_below_frames
#print axioms LightBounceAndCapture.rayStep_of_not_alive
#print axioms LightBounceAndCapture.captured_mapsTo
#print axioms LightBounceAndCapture.captured_stays_captured
#print axioms LightBounceAndCapture.captured_frozen
#print axioms LightBounceAndCapture.lands_inside_captured_forever
#print axioms LightBounceAndCapture.captured_mapsTo_checkFirst
#print axioms LightBounceAndCapture.captured_stays_captured_checkFirst
#print axioms LightBounceAndCapture.tab16_captured_stays
#print axioms LightBounceAndCapture.tab27_captured_stays
#print axioms LightBounceAndCapture.tab28_captured_stays

#print axioms LeechLayers.card_dot_pos_eight
#print axioms LeechLayers.card_dot_neg_eight
#print axioms LeechLayers.card_dot_pos_sixteen
#print axioms LeechLayers.card_dot_neg_sixteen
#print axioms LeechLayers.pos_thirty_two_layer_iff
#print axioms LeechLayers.neg_thirty_two_layer_iff
#print axioms LeechLayers.card_dot_pos_thirty_two
#print axioms LeechLayers.card_dot_neg_thirty_two

#print axioms RingSumMinusTwelfth.two_sin_mul_sin_step
#print axioms RingSumMinusTwelfth.sum_two_sin_mul_sin
#print axioms RingSumMinusTwelfth.bar_sum_eq_two_cot
#print axioms RingSumMinusTwelfth.cos_le_quartic
#print axioms RingSumMinusTwelfth.cot_le
#print axioms RingSumMinusTwelfth.le_cot
#print axioms RingSumMinusTwelfth.cot_sub_inv_div_bounds
#print axioms RingSumMinusTwelfth.tendsto_of_sq_bound
#print axioms RingSumMinusTwelfth.cot_sub_inv_div_tendsto
#print axioms RingSumMinusTwelfth.ringLeftover_eq
#print axioms RingSumMinusTwelfth.ringLeftover_bounds
#print axioms RingSumMinusTwelfth.ring_leftover_tendsto
#print axioms RingSumMinusTwelfth.two_cot_pi_div_48_bounds
#print axioms RingSumMinusTwelfth.bar_sum_24
#print axioms RingSumMinusTwelfth.staircase_hasSum
#print axioms RingSumMinusTwelfth.staircase_tsum
#print axioms RingSumMinusTwelfth.leftover_alg
#print axioms RingSumMinusTwelfth.staircase_poly_bound
#print axioms RingSumMinusTwelfth.exp_quartic_bound
#print axioms RingSumMinusTwelfth.staircaseLeftover_bound
#print axioms RingSumMinusTwelfth.staircase_leftover_tendsto
#print axioms RingSumMinusTwelfth.gap_eq_first_bar_sq
#print axioms RingSumMinusTwelfth.mu_eq_bar_sq
#print axioms RingSumMinusTwelfth.bar_eq_sqrt_mu
#print axioms RingSumMinusTwelfth.sum_sqrt_mu_eq_two_cot
#print axioms LeechLayers.card_dot_layer
#print axioms LeechNorm48Layers.shell_card
#print axioms LeechNorm48Layers.diff_moments
#print axioms LeechLayers.card_norm48_dot_layer

#print axioms LeechLayers.card_norm64_dot_layer

#print axioms LeechShellMoments.diff_moments
#print axioms LeechLayers.card_norm80_dot_layer

#print axioms RamanujanGap.smooth_area
#print axioms RamanujanGap.bars_minus_area_eq_leftover
#print axioms RamanujanGap.smooth_area_cancels
#print axioms RamanujanGap.leftover_dyadic_identity
#print axioms RamanujanGap.alternating_hasSum
#print axioms RamanujanGap.alternating_limit
#print axioms RamanujanGap.finite_leftover_limit_forced
#print axioms RamanujanGap.zeta_neg_one
#print axioms RamanujanGap.leftover_limit_eq_zeta

#print axioms LeechShellCoordinates.card_box_from_choices
#print axioms LeechNorm80Count.choices96
#print axioms LeechNorm80.word_weights
#print axioms LeechLayers.card_shortest_zero_coordinate
#print axioms LeechNorm96.card_norm96_vectors
#print axioms LeechLayers.reference_dot_bounds
#print axioms LeechLayers.reference_layer_card
#print axioms LeechLayers.opposite_layer_count
#print axioms LeechLayers.sum_by_layers
#print axioms LeechLayers.card_norm96_dot_layer

#print axioms GapCrossing.size_zero_iff
#print axioms GapCrossing.size_of_opposite
#print axioms GapCrossing.component_le_size
#print axioms GapCrossing.before_zero
#print axioms GapCrossing.after_zero
#print axioms GapCrossing.real_sign_change_without_zero

-- Continuous Wirtinger and the Riemann-hypothesis investigation.
#print axioms ContinuousWirtinger.dirichlet_energy
#print axioms ContinuousWirtinger.wirtinger
#print axioms ContinuousWirtinger.wirtinger_complex
#print axioms ContinuousWirtinger.zero_gap_sq_lower_bound
#print axioms ContinuousWirtinger.sine_attains_bound
#print axioms RiemannZeroGaps.linePoint_ne_one
#print axioms RiemannZeroGaps.hasDerivAt_zetaLine
#print axioms RiemannZeroGaps.continuous_zetaSlope
#print axioms RiemannZeroGaps.vertical_zero_interval
#print axioms RiemannZeroGaps.vertical_zero_gap
#print axioms RiemannZeroGaps.critical_zero_interval
#print axioms RiemannZeroGaps.zero_on_line
#print axioms RiemannZeroGaps.rh_implies_all_zero_interval
#print axioms RiemannZeroGaps.off_line_zero_refutes_rh
#print axioms RiemannZeroGaps.rh_of_complete_critical_counts
#print axioms RiemannZeroGaps.rh_iff_complete_critical_counts

#print axioms LeechCoordinateTally.card_picks
#print axioms LeechCoordinateTally.tally_eq_fold
#print axioms LeechCoordinateTally.fold_negative
#print axioms LeechCoordinateChoices.charge_nonneg
#print axioms LeechCoordinateChoices.odd_tally
#print axioms LeechShellCoordinates.card_vectors_five_choices
#print axioms LeechNorm80Count.choices112
#print axioms LeechNorm112.card_norm112_vectors
#print axioms LeechLayers.card_norm112_dot_layer

#print axioms LeechCoordinateAlphabet.charge_nonneg
#print axioms LeechCoordinateAlphabet.odd_tally
#print axioms LeechShellCoordinates.card_vectors_six_choices
#print axioms LeechNorm80Count.choices128
#print axioms LeechNorm96.weight_zero
#print axioms LeechNorm96.weight_full
#print axioms LeechNorm128.card_norm128_vectors
#print axioms LeechLayers.card_norm128_dot_layer

#print axioms LeechShellCoordinates.card_vectors_in_six_choice_range
#print axioms LeechNorm80Count.choices144
#print axioms LeechCodeCounts.sum_by_weight
#print axioms LeechNorm144.card_norm144_vectors
#print axioms LeechLayers.card_norm144_dot_layer

#print axioms LeechShellCoordinates.card_vectors_eight_choices
#print axioms LeechNorm80Count.choices160
#print axioms LeechLayers.reference_double_dot_bounds
#print axioms LeechNorm160.card_norm160_vectors
#print axioms LeechLayers.card_norm160_dot_layer

#print axioms LeechNorm80Count.choices176
#print axioms LeechNorm176.card_norm176_vectors
#print axioms LeechLayers.card_norm176_dot_layer

-- Periodic loops
#print axioms loop_wirtinger
#print axioms LoopWirtinger.sine_admissible
#print axioms LoopWirtinger.sine_equality
#print axioms LoopWirtinger.sine_breaks_smaller_constant
#print axioms LoopWirtinger.ring_gap_tendsto

-- Ring spreading inside the store bound
#print axioms WirtingerStore.lets_go_at_least_as_fast
#print axioms WirtingerStore.sum_heatGenerator
#print axioms WirtingerStore.sum_hasDerivAt_zero
#print axioms WirtingerStore.sum_preserved
#print axioms WirtingerStore.mean_zero_preserved
#print axioms WirtingerStore.size_hasDerivAt_dot
#print axioms WirtingerStore.size_hasDerivAt_cost
#print axioms WirtingerStore.size_rate_le
#print axioms WirtingerStore.ring_spreading_le_store
#print axioms WirtingerStore.slowWave_mean_and_cost
#print axioms WirtingerStore.slowWave_size_pos
#print axioms WirtingerStore.slowWave_eigen
#print axioms WirtingerStore.heat_scale
#print axioms WirtingerStore.slowPath_zero
#print axioms WirtingerStore.slowPath_spreads
#print axioms WirtingerStore.slowPath_mean_zero
#print axioms WirtingerStore.slowPath_attains_bound
#print axioms WirtingerStore.faster_rate_fails
#print axioms WirtingerStore.sharp_counterexample

-- Squared length 192
#print axioms LeechNorm80Count.choices192
#print axioms LeechNorm192.card_norm192_vectors
#print axioms LeechLayers.card_norm192_dot_layer

-- Squared length 208
#print axioms LeechNorm80Count.choices208
#print axioms LeechNorm208.card_norm208_vectors
#print axioms LeechLayers.card_norm208_dot_layer
