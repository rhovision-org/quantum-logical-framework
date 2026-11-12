/-
  QLF_AxiomAudit.lean — the dependency footprint of QLF's anchor theorems.

  Zero `sorry` is a weak contract. It says every goal was closed; it says nothing about
  *what closed it*. A theorem proved from definitions and a theorem proved from an opaque
  bridge assumption are epistemically different results, and nothing in the source
  distinguishes them — the bridge can sit twenty imports upstream.

  `#print axioms` answers the question the source cannot: for a given constant, exactly
  which axioms the kernel actually used. This module runs it over the anchors a session
  reasons about most, so the build log carries the answer on every push.

  Reading the output. Three names are Lean's own and appear almost everywhere, because
  Mathlib is classical throughout:

      propext          — propositional extensionality
      Classical.choice — global choice
      Quot.sound       — quotient soundness

  These are *not* a QLF assumption and their presence is not a defect. In particular they
  do not contradict the RCA₀ framing: the reverse-mathematical strength of a *statement*
  is a claim about which subsystem of second-order arithmetic proves it, not about which
  axioms a particular Lean formalisation happened to route through. Mathlib's `Finset`,
  `List` and `ℝ` machinery is classical, so a finitary combinatorial theorem picks up
  `Classical.choice` from its libraries while remaining finitary.

  What matters is the fourth kind of name: anything in the `QLF` namespace. That is a
  project bridge assumption, and it should appear only where the inventory says it does.
  The intended split:

      combinatorial core     — no QLF axiom
      derived physics        — no QLF axiom
      Millennium boundaries  — exactly one named bridge (or the named pair), and no more
      cited external results — the classical theorem QLF declines to reformalise

  The complementary audit is `scripts/axiom_audit.sh`, which pins the *declared* axioms
  (lean/axioms.expected) so no assumption can arrive unnoticed. This file reports what the
  proofs actually consume; that one reports what exists to be consumed.
-/

import QLF_Axioms
import QLF_Universality
import QLF_TwistAlphabet
import QLF_PhaseRule
import QLF_KraftMeasure
import QLF_LatticeCalculus
import QLF_Realizability
import QLF_LawOfExceptions
import QLF_AlphaBound
import QLF_Hodge
import QLF_BSD
import QLF_PvsNP
import QLF_Fredkin
import QLF_HorizonBasis
import QLF_MassGap
import QLF_NavierStokes
import QLF_ChargeBalance
import QLF_CensusCurvature
import QLF_LorentzCover
import QLF_RiemannMRE
import QLF_StationaryAction
import QLF_StationaryPhase
import QLF_ClosureKernel
import QLF_ClosureLeakage
import QLF_ClosureChannels
import QLF_ChannelZeros
import QLF_LightCone
import QLF_RealizableWalk
import QLF_Tsirelson
import QLF_Mass
import QLF_DiracWalk
import QLF_BornFromWays
import QLF_FirstReturn
import QLF_GaugeAxis
import QLF_LocalGauge
import QLF_LatticeGauge
import QLF_Maxwell
import QLF_LinkAction
import QLF_MaxwellTime
import QLF_GaussLaw
import QLF_WalkCoupling
import QLF_CoupledEvolution
import QLF_TsirelsonBound
import QLF_FieldEnergy
import QLF_CompactLinks
import QLF_NonAbelian
import QLF_NonAbelianAction
import QLF_NonAbelianField
import QLF_Courant
import QLF_CompactBound
import QLF_OpticalTheorem
import QLF_ChannelGroupoid
import QLF_PoleFactorization
import QLF_GluonVertex
import QLF_GluonGluing
import QLF_Resonance
import QLF_JointClosure
import QLF_TensorFromClosure
import QLF_VacuumResolvent
import QLF_MixingUnitarity
import QLF_SharedClosure
import QLF_PolaronBranches
import QLF_NonAbelianGauss
import QLF_HiddenZeros
import QLF_HolographicBoundary
import QLF_HolographicArea
import QLF_PlaquetteArea
import QLF_LocalAreaLaw
import QLF_MetricSinglet
import QLF_LatticeDivergence
import QLF_Manifestation
import QLF_StrangeLoop
import QLF_StrangeLoopBorn
import QLF_ConservativeReturn
import QLF_TensorConservativeReturn

-- Paper I v0.3: MO2/QuantumLogic and headline-claim anchors.
-- The baseline for these anchors is intentionally updated only after a
-- reviewed `proof_trust.py --record` run; see Proof_Trust.md.
import QLF_MO2
import QLF_QuantumLogic
import QLF_FineStructureSubstrate
import QLF_AlphaRigidity
import QLF_LenzMassRatio
import QLF_GMinusTwo
import QLF_CosmologicalConstant
import QLF_DarkMatter
import QLF_MondScale
import QLF_RarBalance
import QLF_MercuryPerihelion
import QLF_Discoveries2026
import QLF_StrongCP
import QLF_Majorana

/-! ## The combinatorial core — expected: no QLF axiom -/

#print axioms double_fold_identity
#print axioms QLF.qlf_universality
#print axioms QLF.count_balanced_pauli_closed
#print axioms QLF.PhaseRule.phase_rule
#print axioms QLF.twist_kraft
#print axioms QLF.Realizability.no_continuum_in_finite_region
#print axioms QLF.LawOfExceptions.law_of_exceptions
#print axioms QLF.StationaryAction.balance_is_stationary_mode
#print axioms QLF.StationaryPhase.signed_stationary_phase
#print axioms QLF.StationaryPhase.ways_mode_at_balance

/-! Fredkin's conservative logic identified with ZFA (Fredkin_QLF.md). `fredkin_preserves_zfa`
    runs through the `count_balanced_pauli_closed` keystone, so it must show the Lean three
    and no QLF axiom — the identification is a theorem, not a bridge. -/

#print axioms QLF.Fredkin.fredkin_preserves_zfa
#print axioms QLF.Fredkin.fredkin_bijective

/-! The horizon rebasing. `horizon_rebasis_is_closure_order_iso` must show no QLF axiom — the whole
    point of the module is that the basis algebra is mathematics and the black-hole step is not in
    it. A QLF name here would mean the open bridge had been quietly assumed. -/

#print axioms QLF.HorizonBasis.horizon_rebasis_is_closure_order_iso
#print axioms QLF.HorizonBasis.reachable_rebased_iff

/-! The Yang-Mills measurement. `continuumGap_nonempty` builds a realization by `rfl` and
    `continuumGap_gap_unique` shows the interface pins its own value, so both must show no
    QLF axiom — which is exactly what makes that boundary definitional in Lean. -/

#print axioms QLF.continuumGap_nonempty
#print axioms QLF.continuumGap_gap_unique
#print axioms QLF.mass_gap_quantum_pos

/-! Navier-Stokes: the boundary here was *removed* rather than merged, because
    `continuumClaim_nonempty` shows it assumed nothing — an uninterpreted `Prop` plus its
    truth is satisfied by `True` and `trivial`. What the module still proves stands on its
    own, and must show no QLF axiom. -/

#print axioms QLF.continuumClaim_nonempty
#print axioms QLF.realized_flow_achieves_zfa

/-! Hodge. The two lines belong together: `hodge_realized_on_substrate` (above) is the
    reformulation theorem and carries no QLF axiom, while `algebraicityBridge_nonempty`
    shows the faithfulness bridge is satisfied by reading every class as algebraic. The
    theorem is real and the bridge, in Lean, excludes nothing — that is the whole distinction
    the module's framing turns on. -/

#print axioms QLF.algebraicityBridge_nonempty

/-! The last two, and the contrast between them is the pass's most useful outcome.

    `transportCurvature_nonempty` is trivially satisfiable like the rest — but that reflects
    Mathlib's missing discrete optimal transport, not an empty claim: Jost & Liu (2014) is a
    real theorem, *cited* rather than posited, and discharging it is labour with a known
    answer.

    `properOrthochronous_id` marks the healthy case. `lorentz_generated_by_boosts_rotations`
    quantifies over a fully concrete class with nothing uninterpreted in it, so there is no
    trivial model to exhibit — there is nothing left to choose. That is the standard the
    other boundaries fall short of. -/

/-! Electron capture: the invariants are proved, the rate is not claimed. These must show no QLF
    axiom — the point of proving only the invariants is to keep "allowed" apart from "derived". -/

#print axioms QLF.electron_capture_charge_balanced
#print axioms QLF.capture_changes_exactly_one_slot
#print axioms QLF.local_capture_charge_conserved
#print axioms QLF.electron_capture_factors_through_wminus

#print axioms QLF.transportCurvature_nonempty
#print axioms QLF.LorentzCover.properOrthochronous_id
#print axioms QLF.census_no_triangles

/-! ## Derived results — expected: no QLF axiom.

    `censusTail_eq` is the discharged one: it was a bridge axiom and is now derived from
    Mathlib's generalized binomial theorem, so `QLF_AlphaBound` carries none. If a QLF
    name reappears here, the discharge regressed. -/

#print axioms QLF.AlphaBound.censusTail_eq
#print axioms QLF.LatticeCalculus.field_equations_hold_on_the_lattice

/-! ## Reformulation theorems — expected: no QLF axiom.

    These are the proven halves of the Millennium reformulations. `hodge_realized_on_substrate`
    is the load-bearing case: Hodge classes are exactly the substrate-realized closures, and
    that is proved outright. It must show no QLF axiom — `substrate_realization_is_algebraic`
    is the *next* step, not this one. -/

#print axioms QLF.hodge_realized_on_substrate

/-! `trivial_zero_not_nonTrivial` is the check that the RH boundary now speaks about ζ:
    an ordinary theorem, about Mathlib's `riemannZeta`, carrying no QLF axiom. It could not
    be stated at all while `NonTrivialZero` was an uninterpreted predicate. -/

#print axioms QLF.trivial_zero_not_nonTrivial

/-! `mellinFactorization_iff_rh` measures the Riemann boundary rather than describing it:
    the two-leg Mellin factorization is equivalent to RH, so the middle predicate buys no
    weakening. A theorem about how much an axiom assumes should itself assume nothing, so
    this line must show no QLF axiom. -/

#print axioms QLF.mellinFactorization_iff_rh
#print axioms QLF.mellinFactorization_independent_of_generator

/-! The BSD counterparts. `mirrorInvariant_iff_perspectives_agree` shows the modularity
    mirror carries no strength beyond the agreement it concludes, and
    `mirrorMultiplicity_nonempty` shows the interface is inhabited by constant zero — so a
    construction cannot discharge that boundary the way `QLF_LatticeCalculus` discharged
    its own. Both must show no QLF axiom. -/

#print axioms QLF.mirrorInvariant_iff_perspectives_agree
#print axioms QLF.mirrorMultiplicity_nonempty

/-! The P-vs-NP counterparts. `realized_count_eq_central_binomial` is the module's real
    content — the `C(2n,n)` count of the verify-filtered set — and must carry no QLF axiom.
    `costModel_nonempty` is the measurement: it builds a cost model out of `verify` and
    boolean negation, so it too must carry none, which is precisely what makes it bad news
    for the boundary rather than good. -/

#print axioms QLF.realized_count_eq_central_binomial
#print axioms QLF.costModel_nonempty

/-! ## Boundaries — expected: exactly the named bridge, and nothing further.

    `bsd_rank_equals_order` should consume `bsd_multiplicity` and no other QLF axiom. Note
    what its footprint lacks: `propext`, `Classical.choice` and `Quot.sound` are all absent,
    which is the signature of a pure application — the machine's own way of saying the
    theorem restates its boundary rather than deriving from it. Compare
    `hodge_realized_on_substrate` above, which carries the Lean three and no QLF name: that
    is what a proof looks like.

    `riemann_hypothesis_in_qlf_via_MRE` should consume `mre_factorization` and *not*
    `spectral_hilbert_polya`. The two routes are independent in *dependency* — neither
    proof reaches through the other's axiom, and the first green audit confirmed it — while
    being equivalent in *strength*, since each is equivalent to RH. Both facts are worth
    having and they are different facts; the audit reports the first one. -/

#print axioms QLF.bsd_rank_equals_order
#print axioms QLF.p_vs_np_in_qlf
#print axioms QLF.riemann_hypothesis_in_qlf
#print axioms QLF.riemann_hypothesis_in_qlf_via_MRE

/-! ## Closure algebra (issue #207) — expected: no QLF name

    U1, U2 seed, PZ1, PZ3 and U3 are finite combinatorics over the twist alphabet. Every anchor
    below should carry at most the Lean three. The `native_decide` cross-checks in those modules
    (registry counts, `K_2`, `K_4`) are deliberately not listed: they add `Lean.ofReduceBool` and
    nothing structural depends on them. -/

#print axioms QLF.ClosureUnitarity.history_unitary
#print axioms QLF.ClosureUnitarity.closure_by_dagger
#print axioms QLF.ClosureUnitarity.zero_taxonomy
#print axioms QLF.ClosureUnitarity.antiHermitian_seed_forbidden
#print axioms QLF.ClosureUnitarity.upLeft_forbidden_all_orders
#print axioms QLF.ClosureKernel.closure_factorization
#print axioms QLF.ClosureKernel.vacuum_resolvent_inverse
#print axioms QLF.ClosureKernel.channel_factorization
#print axioms QLF.ClosureKernel.kernel_zero_of_amplitude_zero
#print axioms QLF.ClosureLeakage.leakage_identity
#print axioms QLF.ClosureLeakage.openMass_ge_quarter
#print axioms QLF.ClosureLeakage.open_amplitude
#print axioms QLF.ClosureChannels.channel_last_exit
#print axioms QLF.ClosureChannels.channel_series
#print axioms QLF.ClosureChannels.mixed_channel_zero
#print axioms QLF.ClosureChannels.mixed_open_zero
#print axioms QLF.ClosureChannels.channel_two_sided
#print axioms QLF.ClosureChannels.cone_amplitude
#print axioms QLF.ClosureChannels.cone_zero_iff
#print axioms QLF.ClosureChannels.shellKernel_compose
#print axioms QLF.ClosureChannels.coneStep_unitary
#print axioms QLF.ClosureChannels.shell_total_unitary
#print axioms QLF.ClosureChannels.rawStep_not_unitary
#print axioms QLF.ClosureChannels.realStep_unitary
#print axioms QLF.ClosureChannels.realWalk_unitary
#print axioms QLF.ClosureChannels.realStep_eq_cos_sin
#print axioms QLF.ClosureChannels.realWalk_trace
#print axioms QLF.ClosureChannels.realWalk_trace_even
#print axioms QLF.ClosureChannels.realWalk_neg
#print axioms QLF.ClosureChannels.realWalk_add_star
#print axioms QLF.ClosureChannels.step_forced
#print axioms QLF.ClosureChannels.coinless_step_forced
#print axioms QLF.ClosureChannels.fix_iff_generator
#print axioms QLF.ClosureChannels.coinless_twist_step
#print axioms QLF.ClosureChannels.walk_cos_taylor
#print axioms QLF.ClosureChannels.walk_dispersion_quadratic
#print axioms QLF.ClosureChannels.walk_energy_quadratic
#print axioms QLF.Tsirelson.chsh_sq
#print axioms QLF.Tsirelson.chsh_classical
#print axioms QLF.Tsirelson.chsh_tsirelson
#print axioms QLF.Tsirelson.twistChsh_tsirelson
#print axioms QLF.Tsirelson.twistChsh_sq_e00
#print axioms QLF.Tsirelson.twistChsh_saturates
#print axioms QLF.Mass.weyl_sq
#print axioms QLF.Mass.no_weyl_mass
#print axioms QLF.Mass.dirac_sq
#print axioms QLF.Mass.chirality_comm_dirac
#print axioms QLF.Mass.massStep_unitary
#print axioms QLF.DiracWalk.realWalk_generator
#print axioms QLF.DiracWalk.handed_unitary
#print axioms QLF.DiracWalk.diracWalk_unitary
#print axioms QLF.DiracWalk.diracWalk_generator
#print axioms QLF.DiracWalk.beta_handed_beta
#print axioms QLF.DiracWalk.diracWalk_add_star
#print axioms QLF.DiracWalk.diracWalk_eigen
#print axioms QLF.DiracWalk.diracWalk_dispersion
#print axioms QLF.BornFromWays.born_from_ways
#print axioms QLF.BornFromWays.assignment_unique
#print axioms QLF.GaugeAxis.spacetimeWalk_unitary
#print axioms QLF.GaugeAxis.spacetimeWalk_generator
#print axioms QLF.GaugeAxis.mass_shell
#print axioms QLF.LocalGauge.ringWalk_norm
#print axioms QLF.LocalGauge.ringWalk_covariant
#print axioms QLF.LocalGauge.flux_invariant
#print axioms QLF.LocalGauge.gauge_equiv_of_flux_eq
#print axioms QLF.LatticeGauge.axisStep_norm
#print axioms QLF.LatticeGauge.plaquette_invariant
#print axioms QLF.LatticeGauge.bianchi
#print axioms QLF.LatticeGauge.total_plaquette_zero
#print axioms QLF.Maxwell.continuity
#print axioms QLF.Maxwell.div_curl
#print axioms QLF.Maxwell.gauss_preserved_by_walk
#print axioms QLF.LinkAction.first_variation
#print axioms QLF.LinkAction.stationary_iff_ampere
#print axioms QLF.LinkAction.gauge_invariant_iff_conserved
#print axioms QLF.MaxwellTime.first_variation
#print axioms QLF.MaxwellTime.stationary_iff_update
#print axioms QLF.MaxwellTime.gauss_from_action
#print axioms QLF.GaussLaw.stationary_iff_gauss
#print axioms QLF.GaussLaw.stationary_forces_continuity
#print axioms QLF.GaussLaw.gauge_invariant_iff_continuity
#print axioms QLF.WalkCoupling.link_overlap
#print axioms QLF.WalkCoupling.link_response
#print axioms QLF.CoupledEvolution.evolve_gauss
#print axioms QLF.CoupledEvolution.evolve_norm
#print axioms QLF.CoupledEvolution.evolve_covariant
#print axioms QLF.CoupledEvolution.gauss_neutral
#print axioms QLF.CoupledEvolution.no_background_no_walk
#print axioms QLF.CoupledEvolution.exists_nonzero_admissible
#print axioms QLF.CoupledEvolution.evolve_gauss_neutral
#print axioms QLF.TsirelsonBound.chsh_sos
#print axioms QLF.TsirelsonBound.tsirelson_bound
#print axioms QLF.TsirelsonBound.tsirelson_bound_neg
#print axioms QLF.FieldEnergy.ip_K
#print axioms QLF.FieldEnergy.energy_balance
#print axioms QLF.FieldEnergy.energy_conserved
#print axioms QLF.FieldEnergy.step_energy
#print axioms QLF.FieldEnergy.K_sq_le
#print axioms QLF.FieldEnergy.energy_lower
#print axioms QLF.FieldEnergy.free_stable
#print axioms QLF.FieldEnergy.J_sq_le
#print axioms QLF.FieldEnergy.evolve_sqrt_energy
#print axioms QLF.FieldEnergy.evolve_field_bound
#print axioms QLF.CompactLinks.wilson_variation
#print axioms QLF.CompactLinks.walk_response_sin
#print axioms QLF.CompactLinks.wilson_periodic
#print axioms QLF.CompactLinks.walk_periodic
#print axioms QLF.CompactLinks.compact_gauss_preserved
#print axioms QLF.NonAbelian.step_norm
#print axioms QLF.NonAbelian.step_covariant
#print axioms QLF.NonAbelian.wilson_loop_invariant
#print axioms QLF.NonAbelianAction.plaq_eq_zero_iff
#print axioms QLF.NonAbelianAction.wilson_gauge
#print axioms QLF.NonAbelianAction.wilson_eq_zero_iff
#print axioms QLF.NonAbelianAction.pure_gauge_action
#print axioms QLF.NonAbelianAction.wilson_abelian
#print axioms QLF.NonAbelianField.wilsonOff_bump
#print axioms QLF.NonAbelianField.force_eq
#print axioms QLF.NonAbelianField.stationary_iff
#print axioms QLF.NonAbelianField.yang_mills_iff
#print axioms QLF.Courant.weitzenboeck
#print axioms QLF.Courant.K_sq_le_sharp
#print axioms QLF.Courant.energy_lower_sharp
#print axioms QLF.Courant.free_bounded_sharp
#print axioms QLF.CompactBound.force_le
#print axioms QLF.CompactBound.E_bound
#print axioms QLF.CompactBound.A_bound
#print axioms QLF.OpticalTheorem.optical_iff
#print axioms QLF.OpticalTheorem.optical_forward
#print axioms QLF.OpticalTheorem.history_optical
#print axioms QLF.OpticalTheorem.realWalk_optical
#print axioms QLF.OpticalTheorem.raw_optical_defect
#print axioms QLF.ChannelGroupoid.dag_comp
#print axioms QLF.ChannelGroupoid.hol_dag
#print axioms QLF.ChannelGroupoid.endo_closure
#print axioms QLF.ChannelGroupoid.kernel_compose
#print axioms QLF.ChannelGroupoid.kernel_dagger
#print axioms QLF.PoleFactorization.regular_part
#print axioms QLF.PoleFactorization.rankOne_projector
#print axioms QLF.PoleFactorization.resolvent_partial
#print axioms QLF.PoleFactorization.eig_unit
#print axioms QLF.PoleFactorization.realWalk_poles
#print axioms QLF.GluonVertex.W_mul
#print axioms QLF.GluonVertex.trace_W
#print axioms QLF.GluonVertex.vertex_ne_zero_iff
#print axioms QLF.GluonVertex.gluon_vertex_iff
#print axioms QLF.GluonVertex.two_gluon_commute
#print axioms QLF.GluonVertex.vertex_count
#print axioms QLF.GluonGluing.comm_eq_zero_iff
#print axioms QLF.GluonGluing.chan_ne_zero_iff
#print axioms QLF.GluonGluing.gluing
#print axioms QLF.GluonGluing.jacobi
#print axioms QLF.Resonance.resonance_balance
#print axioms QLF.Resonance.resonance_le_one
#print axioms QLF.Resonance.stable_iff_no_leak
#print axioms QLF.JointClosure.closed_iff_singlet
#print axioms QLF.JointClosure.singlet_corr
#print axioms QLF.JointClosure.singlet_saturates
#print axioms QLF.TensorFromClosure.composite_is_tensor
#print axioms QLF.TensorFromClosure.composite_faithful
#print axioms QLF.TensorFromClosure.joint_fold_determines_pair
#print axioms QLF.TensorFromClosure.pair_scalar_ambiguity
#print axioms QLF.TensorFromClosure.independent_closure_factors
#print axioms QLF.TensorFromClosure.scalar_fold_not_zfa
#print axioms QLF.TensorFromClosure.shared_closure_not_independent
#print axioms QLF.TensorFromClosure.simple_module_is_twoBodyState
#print axioms QLF.TensorFromClosure.n_composite_is_tensor
#print axioms QLF.TensorFromClosure.n_composite_faithful
#print axioms QLF.TensorFromClosure.simple_module_is_cfgState
#print axioms QLF.TensorFromClosure.split_strong_iff_singlet
#print axioms QLF.VacuumResolvent.dyson_unique
#print axioms QLF.VacuumResolvent.chain_tendsto
#print axioms QLF.VacuumResolvent.resummed_is_tower
#print axioms QLF.VacuumResolvent.landau_capacity
#print axioms QLF.MixingUnitarity.block_unitary_iff
#print axioms QLF.MixingUnitarity.triangle_closes
#print axioms QLF.MixingUnitarity.jarlskog_invariant
#print axioms QLF.SharedClosure.bonding_above
#print axioms QLF.SharedClosure.symmetric_split
#print axioms QLF.SharedClosure.feshbach_entry
#print axioms QLF.PolaronBranches.branch_iff
#print axioms QLF.PolaronBranches.attractive_exists
#print axioms QLF.PolaronBranches.zero_at_bath
#print axioms QLF.PolaronBranches.f_deriv
#print axioms QLF.NonAbelianGauss.noether
#print axioms QLF.NonAbelianGauss.gauss_covariant
#print axioms QLF.HiddenZeros.A4_zero
#print axioms QLF.HiddenZeros.A5_zero
#print axioms QLF.HiddenZeros.A5_near_zero
#print axioms QLF.HolographicBoundary.closure_iff_boundary_silent
#print axioms QLF.HolographicBoundary.every_prefix_closes
#print axioms QLF.HolographicBoundary.cutEntropy_le_area
#print axioms QLF.HolographicBoundary.nonlocal_pairs_break_area_law
#print axioms QLF.HolographicArea.light_cone
#print axioms QLF.HolographicArea.pair_range_le
#print axioms QLF.HolographicArea.horizon_area_law
#print axioms QLF.PlaquetteArea.holonomy_eq_area_parity
#print axioms QLF.PlaquetteArea.holonomy_eq_projected_areas
#print axioms QLF.PlaquetteArea.fold_eq_projected_phase
#print axioms QLF.LocalAreaLaw.local_area_law
#print axioms QLF.MetricSinglet.metric_is_singlet
#print axioms QLF.MetricSinglet.expect_twoBody
#print axioms QLF.MetricSinglet.product_annihilator_iff_singlet
#print axioms QLF.LatticeDivergence.latticeCalculus
#print axioms QLF.LatticeDivergence.lattice_einstein_field_equations


/-! ## Paper I v0.3 — MO2 / QuantumLogic G1 anchors

These are the exact anchors proposed in Paper I v0.3 Appendix A.  The
`True := trivial` summary markers (`quantum_logic_summary`,
`MO2_is_quantum_logic`) are intentionally NOT anchored.  Baseline updates
require a reviewed `proof_trust.py --record` run; see Proof_Trust.md. -/

-- MO2: existing core theorems
#print axioms QLF.MO2.le_refl
#print axioms QLF.MO2.le_trans
#print axioms QLF.MO2.le_antisymm
#print axioms QLF.MO2.compl_involutive
#print axioms QLF.MO2.compl_antitone
#print axioms QLF.MO2.inf_compl_bot
#print axioms QLF.MO2.sup_compl_top
#print axioms QLF.MO2.orthomodular
#print axioms QLF.MO2.not_distributive

-- MO2: new lub/glb/absorption laws
#print axioms QLF.MO2.le_sup_left
#print axioms QLF.MO2.le_sup_right
#print axioms QLF.MO2.sup_le
#print axioms QLF.MO2.inf_le_left
#print axioms QLF.MO2.inf_le_right
#print axioms QLF.MO2.le_inf
#print axioms QLF.MO2.sup_inf_absorb
#print axioms QLF.MO2.inf_sup_absorb

-- QuantumLogic: existing core theorems
#print axioms QLF.QuantumLogic.le_refl
#print axioms QLF.QuantumLogic.le_trans
#print axioms QLF.QuantumLogic.le_antisymm
#print axioms QLF.QuantumLogic.compl_involutive
#print axioms QLF.QuantumLogic.compl_antitone
#print axioms QLF.QuantumLogic.inf_compl_bot
#print axioms QLF.QuantumLogic.sup_compl_top
#print axioms QLF.QuantumLogic.orthomodular
#print axioms QLF.QuantumLogic.not_distributive
#print axioms QLF.QuantumLogic.incompatibility_source

-- QuantumLogic: new lub/glb/absorption laws
#print axioms QLF.QuantumLogic.le_sup_left
#print axioms QLF.QuantumLogic.le_sup_right
#print axioms QLF.QuantumLogic.sup_le
#print axioms QLF.QuantumLogic.inf_le_left
#print axioms QLF.QuantumLogic.inf_le_right
#print axioms QLF.QuantumLogic.le_inf
#print axioms QLF.QuantumLogic.sup_inf_absorb
#print axioms QLF.QuantumLogic.inf_sup_absorb

/-! ## Paper I v0.3 — headline-claim anchors

Substantive theorem anchors for the claims in the paper's positive claims
table.  The `True := trivial` summary markers in these modules are NOT anchors. -/

-- Fine-structure alpha
#print axioms QLF.alpha_QLF_eq
#print axioms QLF.alpha_bare_eq
#print axioms QLF.AlphaBound.leadInv_eq
#print axioms QLF.AlphaBound.codata_in_exact_census_band
#print axioms QLF.AlphaBound.codata_residual_in_census_bracket
#print axioms QLF.AlphaRigidity.inverseAlpha_at_three
#print axioms QLF.AlphaRigidity.alpha_unique

-- m_p / m_e
#print axioms QLF.lenz_factor_eq
#print axioms QLF.mass_ratio_QLF_eq

-- g - 2
#print axioms QLF.a_e_QLF_eq_schwinger
#print axioms QLF.a_e_QLF_substrate
#print axioms QLF.g_factor_QLF_eq

-- Omega_Lambda
#print axioms QLF.Omega_Lambda_4_gauge_eq
#print axioms QLF.Omega_Lambda_0_gauge_eq
#print axioms QLF.only_2_gauge_matches_observed_Omega_Lambda

-- Dark matter / RAR
#print axioms QLF.mond_acceleration_horizon_form
#print axioms QLF.radialAccel_self_consistent
#print axioms QLF.MondScale.a0_is_hubble_per_closure_loop
#print axioms QLF.MondScale.a0_eq_c_times_cyclic_rate
#print axioms QLF.rar_is_free_energy_balance

-- Mercury perihelion
#print axioms QLF.perihelion_advance_per_century_eq
#print axioms QLF.perihelion_advance_form_equivalence

-- Alpha cannot drift (kill-condition anchor)
#print axioms QLF.Discoveries2026.alpha_cannot_drift

-- Born rule: `QLF.BornFromWays.born_from_ways` and `assignment_unique` are
-- already anchored in the BornFromWays section above; do not duplicate them.

-- Strong CP / no axion (kill-condition anchor)
#print axioms QLF.theta_zero_on_closure

-- CPT / antiparticle time mirror (kill-condition anchors)
#print axioms QLF.Discoveries2026.antiparticle_length
#print axioms QLF.Discoveries2026.charge3W_antiparticle
#print axioms QLF.Majorana.neutrino_majorana

/-! ## QLF_Manifestation — orientation, isolation, unbounded closures, distance = delay, proton

These anchors are added by PR #226 and reviewed in the 319-anchor baseline. -/

#print axioms QLF.Manifestation.completion_net_determined
#print axioms QLF.Manifestation.isolated_iff_closed
#print axioms QLF.Manifestation.isolation_interleaved
#print axioms QLF.Manifestation.closed_insertion_is_phase
#print axioms QLF.Manifestation.closures_unbounded
#print axioms QLF.Manifestation.prime_closure_every_length
#print axioms QLF.Manifestation.distance_eq_delay
#print axioms QLF.Manifestation.same_niches_iff_sameNet
#print axioms QLF.Manifestation.rearrangement_neutral
#print axioms QLF.Manifestation.short_closures_unwound
#print axioms QLF.Manifestation.proton_simplest_isolated_imbalance
#print axioms QLF.Manifestation.proton_ways_unbounded

/-! ## Conservative-return and tensor-return anchors

These anchors are added by PR #230. They are the toy conservative-return
interface, the finite Born return, the trigger/quotient structures, and the
tensor quotient return. They are part of the 343-anchor baseline. -/

#print axioms QLF.StrangeLoop.conservative_return
#print axioms QLF.StrangeLoop.return_forward
#print axioms QLF.StrangeLoop.F_preserves_le
#print axioms QLF.StrangeLoop.R_preserves_le
#print axioms QLF.StrangeLoop.F_preserves_sup
#print axioms QLF.StrangeLoop.F_preserves_inf
#print axioms QLF.StrangeLoop.F_preserves_compl

#print axioms QLF.StrangeLoop.refinement_return
#print axioms QLF.StrangeLoop.born_return
#print axioms QLF.StrangeLoop.born_two_thirds_return

#print axioms QLF.ConservativeReturn.conservative_return
#print axioms QLF.ConservativeReturn.F_closed
#print axioms QLF.ConservativeReturn.count_recovered
#print axioms QLF.ConservativeReturn.phase_recovered
#print axioms QLF.ConservativeReturn.F_invariants
#print axioms QLF.ConservativeReturn.toyTrigger_exists
#print axioms QLF.ConservativeReturn.toyTrigger_composite
#print axioms QLF.ConservativeReturn.toyQuotientTrigger_exists
#print axioms QLF.ConservativeReturn.no_event_cycle

#print axioms QLF.TensorConservativeReturn.tensor_conservative_return
#print axioms QLF.TensorConservativeReturn.tensorTrigger_exists
#print axioms QLF.TensorConservativeReturn.class_of_step
#print axioms QLF.TensorConservativeReturn.F_injective
#print axioms QLF.TensorConservativeReturn.R_forward
#print axioms QLF.FirstReturn.prime_event_reciprocal_open
