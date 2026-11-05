import QLF_GluonVertex

/-!
# QLF_GluonGluing — four-gluon colour factors by gluing two vertices (G2, colour part)

Issue #207, target **G2**: build the four-gluon amplitude by gluing three-gluon closures, with
residues that factor into lower-point kernels. This module does the colour part, on the Weyl
operators of [`QLF_GluonVertex`](QLF_GluonVertex.lean).

* **`comm_eq`, `comm_eq_zero_iff`.** `[W(p), W(q)] = (ω^{p₂q₁} − ω^{q₂p₁}) W(p + q)`: a bracket of
  two gluons is one gluon, labelled by the sum, and it vanishes exactly when `⟨p, q⟩ = 0`.
* **`chan`.** The `s`-channel colour factor `c_s = tr([W(p), W(q)] [W(r), W(s)])`.
* **`chan_ne_zero_iff`.** `c_s ≠ 0` iff `p + q + r + s = 0`, `⟨p, q⟩ ≠ 0` and `⟨r, s⟩ ≠ 0`: the four
  labels close, and each pair closes into a bracket.
* **`gluing`.** When the four labels close, with `e = p + q` the intermediate gluon,
  `tr(W(−e) W(e)) · c_s = V(−e, p, q) · V(e, r, s)`, and `tr(W(−e) W(e)) ≠ 0` (`prop_ne_zero`).
  The four-gluon colour factor is the product of two three-gluon vertices divided by the
  intermediate gluon's norm: it factors through one intermediate closure.
* **`jacobi`.** `c_s + c_t + c_u = 0` for the three channels. The colour factors of the three ways
  to glue are not independent; one is fixed by the other two.
* **`chan_count`.** Of the 456 colour-balanced ordered quadruples of twists, 288 have a nonzero
  `s`-channel factor; in the other 168 the `s` channel vanishes structurally (no bracket closes).

**Not here.** The kinematic factors, so the full four-gluon amplitude and its residues in the
Mandelstam variables (G2b), and hidden zeros (G2c), which are kinematic. The colour side of G2 is
done: gluing, factorization through the intermediate gluon, and the Jacobi relation. No axioms.

**Credit.** Colour decomposition and the Jacobi relation among channel colour factors are standard
(e.g. Dixon, *Calculating scattering amplitudes efficiently*, TASI 1995, hep-ph/9601359); the
relation `c_s + c_t + c_u = 0` is the colour side of Bern, Carrasco and Johansson's
colour–kinematics duality (*Phys. Rev. D* **78**, 085011 (2008)). Part of the
[Quantum Logical Framework (QLF)](../README.md).
-/

namespace QLF.GluonGluing

open Matrix QLF QLF.ColourFlux QLF.GluonVertex Fin.CommRing

/-- The commutator of two Weyl operators. -/
noncomputable def comm (p q : V) : Matrix F3 F3 ℂ := W p * W q - W q * W p

/-- **A bracket of two gluons is one gluon.** -/
theorem comm_eq (p q : V) : comm p q = (wp (p.2 * q.1) - wp (q.2 * p.1)) • W (p + q) := by
  unfold comm; rw [W_mul, W_mul, add_comm q p, sub_smul]

lemma W_ne_zero (p : V) : W p ≠ 0 := by
  intro h
  have := congrFun (congrFun h (0 + p.1)) 0
  simp [W] at this
  exact wp_ne_zero _ this

lemma coef_eq_zero_iff (p q : V) : wp (p.2 * q.1) - wp (q.2 * p.1) = 0 ↔ symp p q = 0 := by
  rw [sub_eq_zero]
  constructor
  · intro h; have := wp_injective _ _ h; unfold symp; linear_combination -this
  · intro h; congr 1; unfold symp at h; linear_combination -h

/-- **The bracket vanishes exactly when the labels are collinear.** -/
theorem comm_eq_zero_iff (p q : V) : comm p q = 0 ↔ symp p q = 0 := by
  rw [comm_eq, smul_eq_zero, coef_eq_zero_iff]
  exact or_iff_left (W_ne_zero _)

/-- **The channel colour factor** `tr([W(p), W(q)] [W(r), W(s)])`. -/
noncomputable def chan (p q r s : V) : ℂ := trace (comm p q * comm r s)

lemma tr_WW (u v : V) : trace (W u * W v) = wp (u.2 * v.1) * trace (W (u + v)) := by
  rw [W_mul, trace_smul, smul_eq_mul]

theorem chan_eq (p q r s : V) : chan p q r s =
    (wp (p.2 * q.1) - wp (q.2 * p.1)) * (wp (r.2 * s.1) - wp (s.2 * r.1)) *
      (wp ((p + q).2 * (r + s).1) * trace (W (p + q + (r + s)))) := by
  unfold chan
  rw [comm_eq, comm_eq, Matrix.smul_mul, Matrix.mul_smul, smul_smul, trace_smul, smul_eq_mul, tr_WW]

/-- **The `s` channel is nonzero iff the four labels close and each pair brackets.** -/
theorem chan_ne_zero_iff (p q r s : V) :
    chan p q r s ≠ 0 ↔ p + q + r + s = 0 ∧ symp p q ≠ 0 ∧ symp r s ≠ 0 := by
  rw [chan_eq, trace_W, show p + q + (r + s) = p + q + r + s by abel]
  by_cases h : p + q + r + s = 0
  · simp only [h, ite_true, true_and, ne_eq, mul_eq_zero, not_or, coef_eq_zero_iff]
    have h3 : (3 : ℂ) ≠ 0 := by norm_num
    simp [h3, wp_ne_zero]
  · simp [h]

/-- The intermediate gluon's norm `tr(W(−e) W(e))` never vanishes. -/
theorem prop_ne_zero (e : V) : trace (W (-e) * W e) ≠ 0 := by
  rw [tr_WW, neg_add_cancel, trace_W]
  simp [wp_ne_zero]

/-- **Gluing.** The four-gluon colour factor is two three-gluon vertices over the intermediate
    gluon's norm: `tr(W(−e) W(e)) · c_s = V(−e, p, q) · V(e, r, s)` with `e = p + q`. -/
theorem gluing (p q r s : V) (h : p + q + r + s = 0) :
    trace (W (-(p + q)) * W (p + q)) * chan p q r s =
      vertex (-(p + q)) p q * vertex (p + q) r s := by
  have hrs : r + s = -(p + q) := by rw [← sub_eq_zero, sub_neg_eq_add]; rw [← h]; abel
  unfold chan vertex
  rw [show W q * W p = W q * W p from rfl, ← comm, ← comm, comm_eq, comm_eq, hrs]
  simp only [Matrix.smul_mul, Matrix.mul_smul, trace_smul, smul_eq_mul]
  rw [trace_mul_comm (W (p + q)) (W (-(p + q)))]
  ring

lemma tr_comm_comm (X C D : Matrix F3 F3 ℂ) :
    trace (X * (C * D - D * C)) = trace ((X * C - C * X) * D) := by
  rw [Matrix.mul_sub, Matrix.sub_mul, trace_sub, trace_sub, ← Matrix.mul_assoc X C D,
    ← Matrix.mul_assoc X D C, trace_mul_comm (X * D) C, ← Matrix.mul_assoc C X D]

/-- **The Jacobi relation among the three channels**: `c_s + c_t + c_u = 0`. -/
theorem jacobi (p q r s : V) : chan p q r s + chan q r p s + chan r p q s = 0 := by
  unfold chan comm
  rw [tr_comm_comm, tr_comm_comm, tr_comm_comm, ← trace_add, ← trace_add, ← Matrix.add_mul,
    ← Matrix.add_mul]
  have hj : ((W p * W q - W q * W p) * W r - W r * (W p * W q - W q * W p)) +
      ((W q * W r - W r * W q) * W p - W p * (W q * W r - W r * W q)) +
      ((W r * W p - W p * W r) * W q - W q * (W r * W p - W p * W r)) = 0 := by noncomm_ring
  rw [hj, Matrix.zero_mul, trace_zero]

set_option maxRecDepth 100000 in
/-- **288 of the 456 colour-balanced ordered twist quadruples have a nonzero `s` channel.** -/
theorem chan_count :
    ((allTwists.toFinset ×ˢ allTwists.toFinset ×ˢ allTwists.toFinset ×ˢ allTwists.toFinset).filter
      (fun x => colVec x.1 + colVec x.2.1 + colVec x.2.2.1 + colVec x.2.2.2 = 0)).card = 456 ∧
    ((allTwists.toFinset ×ˢ allTwists.toFinset ×ˢ allTwists.toFinset ×ˢ allTwists.toFinset).filter
      (fun x => colVec x.1 + colVec x.2.1 + colVec x.2.2.1 + colVec x.2.2.2 = 0 ∧
        symp (colVec x.1) (colVec x.2.1) ≠ 0 ∧
        symp (colVec x.2.2.1) (colVec x.2.2.2) ≠ 0)).card = 288 := by
  decide

end QLF.GluonGluing
