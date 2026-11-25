import QLF_Minkowski
import QLF_ClockPairing
import QLF_Motives
import QLF_Handedness

/-!
# The time-reversed universe exists only by perspective

Companion: [`Time_Reversed_Universe.md`](../Time_Reversed_Universe.md), issue #236.

Jim (2026-11-25): *"The interval is by perspective. … The time reverse universe. No singular
reverse time perspective universe, except by perspective."*

This module separates the parts of that statement that are theorems from the parts that are
readings. Three layers.

**§1 The interval and its split.** The interval `t² − x² − y² − z²` is the same in every
perspective (`lorentz_preserves_interval`, and here `boost_interval` for an explicit real boost
family). What *is* by perspective is its split into a time part and a space part: one boost
turns a pure-time separation into one with nonzero space part (`split_by_perspective`). The
time reversal `t ↦ −t` also preserves the interval (`timeReverse_interval`), so the interval
cannot tell a history from its reversed reading.

**§2 Which order is by perspective, and which is not.** For a spacelike separation the sign of
`Δt` is set by the perspective: two boosts in the family give opposite signs
(`spacelike_order_by_perspective`). For a timelike or null separation every boost in the
family keeps the sign (`timelike_order_invariant`, `null_order_invariant`), and no congruence
`X ↦ A X A†` at all sends the unit time direction to its reverse (`no_congruence_reverses_time`).
So the time-reversed reading of a causal (timelike or null) separation is never reached by a
change of inertial perspective. Light-cone membership is perspective-independent
(`timeReverse_null_iff`, `boost_null_iff`).

**§3 The reversed census is the census.** On finite twist histories, reversal and the
conjugate-reverse `dagger` both map the set of closures onto itself
(`reverse_closure_iff`, `dagger_closure_iff`), and on paired clock-domain histories the map `J`
of [`QLF_ClockPairing`](QLF_ClockPairing.lean) maps the admissible set onto itself
(`J_admissible_iff`, `reversed_census_is_census`). So the reversed universe is not a second
collection of histories: it is the same collection, read from the other end or from the other
domain. Some histories are their own reversed reading (`self_reversed_exists`,
`J_not_fixed_point_free`) and some are not (`reversed_reading_distinct`), so whether the
reversed reading names a different history depends on the history.

What is **not** derived: that nature contains a counterpart domain, that `J` is physical time
reversal, any horizon or no-signalling law, or any age relation. No axiom is added.
-/

namespace QLF.TimeReversalPerspective

open QLF QLF.Minkowski QLF.ClockDomains QLF.ClockPairing QLF.ClosureUnitarity Matrix

-- ==========================================
-- §1  The interval is invariant; its split is by perspective
-- ==========================================

/-- Time reversal of a separation: `t ↦ −t`, space unchanged. -/
def timeReverse (f : Form) : Form := ⟨-f.t, f.x, f.y, f.z⟩

theorem timeReverse_involutive (f : Form) : timeReverse (timeReverse f) = f := by
  cases f; simp [timeReverse]

/-- **The interval cannot tell a separation from its time-reversed reading.** -/
theorem timeReverse_interval (f : Form) : Form.interval (timeReverse f) = Form.interval f := by
  unfold Form.interval timeReverse; ring

/-- The boost along `z` with parameters `γ = c`, `γβ = s`, where `c² − s² = 1`, `c > 0`. -/
def boost (c s : ℝ) (f : Form) : Form := ⟨c * f.t + s * f.z, f.x, f.y, s * f.t + c * f.z⟩

/-- **Every boost of the family preserves the interval.** -/
theorem boost_interval (c s : ℝ) (hcs : c ^ 2 - s ^ 2 = 1) (f : Form) :
    Form.interval (boost c s f) = Form.interval f := by
  unfold Form.interval boost
  simp only
  have : (c * f.t + s * f.z) ^ 2 - (s * f.t + c * f.z) ^ 2 = (c ^ 2 - s ^ 2) * (f.t ^ 2 - f.z ^ 2) := by
    ring
  rw [hcs, one_mul] at this
  linarith

/-- The concrete boost `γ = 5/4`, `γβ = 3/4` (velocity `3/5`) and its inverse. -/
theorem fiveFour_ok : (5 / 4 : ℝ) ^ 2 - (3 / 4) ^ 2 = 1 := by norm_num
theorem fiveFour_inv_ok : (5 / 4 : ℝ) ^ 2 - (-3 / 4) ^ 2 = 1 := by norm_num

/-- The rest separation: one unit of time, no space. -/
def restTick : Form := ⟨1, 0, 0, 0⟩

/-- **The split is by perspective.** The rest tick is pure time in its own perspective; in the
    boosted perspective it has time part `5/4` and space part `3/4`. The interval is `1` in both. -/
theorem split_by_perspective :
    restTick.t = 1 ∧ restTick.z = 0 ∧
      (boost (5/4) (3/4) restTick).t = 5/4 ∧ (boost (5/4) (3/4) restTick).z = 3/4 ∧
      Form.interval (boost (5/4) (3/4) restTick) = Form.interval restTick ∧
      Form.interval restTick = 1 := by
  refine ⟨rfl, rfl, ?_, ?_, boost_interval _ _ fiveFour_ok _, ?_⟩ <;>
    simp [boost, restTick, Form.interval]

-- ==========================================
-- §2  Spacelike order is by perspective; causal order is not
-- ==========================================

/-- A spacelike separation: no time part, one unit of space. -/
def spaceTick : Form := ⟨0, 0, 0, 1⟩

theorem spaceTick_spacelike : Form.interval spaceTick < 0 := by
  simp [spaceTick, Form.interval]

/-- **For a spacelike separation, which event is first is by perspective.** One boost puts it
    in the future (`Δt = 3/4`), the inverse boost in the past (`Δt = −3/4`). -/
theorem spacelike_order_by_perspective :
    0 < (boost (5/4) (3/4) spaceTick).t ∧ (boost (5/4) (-3/4) spaceTick).t < 0 := by
  constructor <;> (simp [boost, spaceTick]; try norm_num)

/-- **For a future timelike separation, every boost in the family keeps it in the future.** -/
theorem timelike_order_invariant (c s : ℝ) (hcs : c ^ 2 - s ^ 2 = 1) (hc : 0 < c)
    (f : Form) (ht : 0 < f.t) (hint : 0 < Form.interval f) : 0 < (boost c s f).t := by
  unfold Form.interval at hint
  simp only [boost]
  have hz : f.z ^ 2 < f.t ^ 2 := by nlinarith [sq_nonneg f.x, sq_nonneg f.y]
  have h1 : (s * f.z) ^ 2 < (c * f.t) ^ 2 := by
    have : (c * f.t) ^ 2 = (1 + s ^ 2) * f.t ^ 2 := by rw [mul_pow]; congr 1; linarith
    rw [this, mul_pow]; nlinarith [sq_nonneg s, sq_pos_of_pos ht]
  have h2 : 0 < c * f.t := mul_pos hc ht
  by_contra hneg
  push Not at hneg
  have h3 : s * f.z - c * f.t < 0 := by linarith
  have h4 := mul_nonneg_of_nonpos_of_nonpos hneg h3.le
  nlinarith [h4, h1]

/-- **The same for a future null separation with nonzero time part** (light). -/
theorem null_order_invariant (c s : ℝ) (hcs : c ^ 2 - s ^ 2 = 1) (hc : 0 < c)
    (f : Form) (ht : 0 < f.t) (hnull : Form.interval f = 0) : 0 < (boost c s f).t := by
  unfold Form.interval at hnull
  simp only [boost]
  have hz : f.z ^ 2 ≤ f.t ^ 2 := by nlinarith [sq_nonneg f.x, sq_nonneg f.y]
  have hc1 : s ^ 2 < c ^ 2 := by linarith
  have h1 : (s * f.z) ^ 2 < (c * f.t) ^ 2 := by
    rw [mul_pow, mul_pow]
    have := sq_pos_of_pos ht
    nlinarith [sq_nonneg s, sq_nonneg f.z]
  have h2 : 0 < c * f.t := mul_pos hc ht
  by_contra hneg
  push Not at hneg
  have h3 : s * f.z - c * f.t < 0 := by linarith
  have h4 := mul_nonneg_of_nonpos_of_nonpos hneg h3.le
  nlinarith [h4, h1]

/-- **Light-cone membership is perspective-independent**, under boosts and under reversal. -/
theorem boost_null_iff (c s : ℝ) (hcs : c ^ 2 - s ^ 2 = 1) (f : Form) :
    Form.interval (boost c s f) = 0 ↔ Form.interval f = 0 := by
  rw [boost_interval c s hcs]

theorem timeReverse_null_iff (f : Form) :
    Form.interval (timeReverse f) = 0 ↔ Form.interval f = 0 := by
  rw [timeReverse_interval]

/-- **The time-reversed reading of a future causal separation is not a perspective in the
    boost family**: the family keeps `Δt > 0`, reversal makes it negative. -/
theorem timeReverse_not_a_boost (c s : ℝ) (hcs : c ^ 2 - s ^ 2 = 1) (hc : 0 < c) :
    boost c s restTick ≠ timeReverse restTick := by
  intro h
  have hpos := timelike_order_invariant c s hcs hc restTick (by simp [restTick])
    (by simp [restTick, Form.interval])
  rw [h] at hpos
  simp [timeReverse, restTick] at hpos
  linarith

/-- **No congruence reverses the unit time direction.** For every `A` (in particular every
    `A ∈ SL(2,ℂ)`, every Lorentz perspective), `A · I · A† ≠ −I`: the `(0,0)` entry of
    `A A†` is `|a₀₀|² + |a₀₁|² ≥ 0`, while that of `−I` is `−1`. -/
theorem no_congruence_reverses_time (A : Matrix (Fin 2) (Fin 2) ℂ) :
    A * 1 * Aᴴ ≠ -1 := by
  intro h
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => (M 0 0).re) h
  simp only [Matrix.mul_one, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply,
    Matrix.neg_apply, Matrix.one_apply_eq, Complex.add_re, Complex.mul_re, Complex.neg_re,
    Complex.one_re, Complex.star_def, Complex.conj_re, Complex.conj_im] at h00
  nlinarith [sq_nonneg (A 0 0).re, sq_nonneg (A 0 0).im, sq_nonneg (A 0 1).re,
    sq_nonneg (A 0 1).im]

-- ==========================================
-- §3  The reversed census is the census
-- ==========================================

/-- Reversal of a single word is an involution on closures: a word closes iff its reversed
    reading closes. -/
theorem reverse_closure_iff (w : List Twist) : countBalanced w.reverse ↔ countBalanced w := by
  constructor
  · intro h; simpa using QLF.countBalanced_reverse h
  · exact QLF.countBalanced_reverse

/-- The conjugate-reverse reading too. -/
theorem dagger_closure_iff (w : List Twist) : countBalanced (dagger w) ↔ countBalanced w := by
  unfold countBalanced
  simp only [count_dagger, Twist.conj]
  constructor <;> rintro ⟨h1, h2, h3, h4⟩ <;> exact ⟨by omega, by omega, by omega, by omega⟩

/-- `J` preserves and reflects admissibility. -/
theorem J_admissible_iff (h : History) : admissible (J h) ↔ admissible h := by
  constructor
  · intro hJ; simpa [J_involutive] using J_admissible (J h) hJ
  · exact J_admissible h

/-- **The reversed census is the census.** Every admissible paired history is the reversed
    reading of an admissible paired history (namely its own `J`). There is no second collection. -/
theorem reversed_census_is_census (h : History) :
    admissible h ↔ ∃ k : History, admissible k ∧ J k = h := by
  constructor
  · intro hh; exact ⟨J h, J_admissible h hh, J_involutive h⟩
  · rintro ⟨k, hk, rfl⟩; exact J_admissible k hk

/-- Some closures are their own reversed reading … -/
theorem self_reversed_exists :
    countBalanced [Twist.up, Twist.down] ∧ [Twist.up, Twist.down].reverse ≠ [Twist.up, Twist.down] ∧
      dagger [Twist.up, Twist.down] = [Twist.up, Twist.down] := by
  refine ⟨?_, ?_, ?_⟩
  · unfold countBalanced; decide
  · decide
  · decide

/-- … and some are not: a closed plaquette whose reversed reading is a different closure. -/
theorem reversed_reading_distinct :
    countBalanced [Twist.up, Twist.left, Twist.down, Twist.right] ∧
      countBalanced [Twist.up, Twist.left, Twist.down, Twist.right].reverse ∧
      [Twist.up, Twist.left, Twist.down, Twist.right].reverse ≠
        [Twist.up, Twist.left, Twist.down, Twist.right] ∧
      dagger [Twist.up, Twist.left, Twist.down, Twist.right] ≠
        [Twist.up, Twist.left, Twist.down, Twist.right] := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold countBalanced; decide
  · unfold countBalanced; decide
  · decide
  · decide

/-- **Each domain reads its own clock forward.** Under `J` the counterpart's tick `i` is our
    tick `n − 1 − i` conjugated: the reversal is a relation between two readings, and neither
    reading runs backward in itself. (Restates `dagger_tick` in this module's vocabulary.) -/
theorem each_reads_forward (w : List Twist) (i : ℕ) (hi : i < w.length) :
    (dagger w)[i]? = (w[w.length - 1 - i]?).map Twist.conj :=
  dagger_tick w i hi

-- ==========================================
-- §4  Handedness is the distinction
-- ==========================================

/-- Pure order reversal leaves every component of handedness unchanged. -/
theorem handednessOn_reverse (a : Axis) (w : List Twist) :
    handednessOn a w.reverse = handednessOn a w := by
  simp [handednessOn, List.count_reverse]

/-- The conjugate-reverse reading negates every component of handedness. -/
theorem handednessOn_dagger (a : Axis) (w : List Twist) :
    handednessOn a (dagger w) = - handednessOn a w := by
  unfold QLF.ClosureUnitarity.dagger
  rw [handednessOn_reverse, handednessOn_map_conj]

/-- **Handedness is the distinction, event by event.** The reversed reading's tick `i` is our
    tick `n − 1 − i` with its handedness reversed, and handedness is never zero, so every event
    of the reversed reading differs from its partner in handedness. -/
theorem reversed_tick_opposite_handedness (w : List Twist) (i : ℕ) (hi : i < w.length) :
    ∃ t : Twist, w[w.length - 1 - i]? = some t ∧ (dagger w)[i]? = some t.conj ∧
      handedness t.conj = - handedness t ∧ handedness t ≠ 0 := by
  have hj : w.length - 1 - i < w.length := by omega
  refine ⟨w[w.length - 1 - i], List.getElem?_eq_getElem hj, ?_, handedness_conj _,
    handedness_ne_zero _⟩
  rw [dagger_tick w i hi, List.getElem?_eq_getElem hj]
  rfl

/-- **On a closure, the totals cannot tell the two readings apart**: net handedness is zero on
    every axis in both. The distinction lives in the events, not in the totals. -/
theorem closure_totals_blind (w : List Twist) (hw : countBalanced w) (a : Axis) :
    handednessOn a (dagger w) = 0 ∧ handednessOn a w = 0 := by
  have h := (zfa_iff_handedness_balanced w).1 hw a
  exact ⟨by rw [handednessOn_dagger, h, neg_zero], h⟩

/-- **Order reversal without handedness reversal is a different reading.** For the plaquette
    `[up, left, down, right]` the pure reversal and the conjugate-reverse are different words:
    what separates them is handedness alone. -/
theorem reversal_vs_dagger_differ :
    [Twist.up, Twist.left, Twist.down, Twist.right].reverse ≠
      dagger [Twist.up, Twist.left, Twist.down, Twist.right] := by
  decide

-- ==========================================
-- §5  Every possible reversed reading exists, and each is inside the census
-- ==========================================

/-- Reverse handedness on the axes `s` selects, keep it on the others. -/
def flipBy (s : Axis → Bool) (t : Twist) : Twist := if s (twistAxis t) then t.conj else t

/-- A reversed reading: reverse the order, and reverse handedness on the axes `s` selects.
    `s` constant `false` is pure reversal; `s` constant `true` is `dagger`. -/
def readingBy (s : Axis → Bool) (w : List Twist) : List Twist := (w.map (flipBy s)).reverse

theorem twistAxis_flipBy (s : Axis → Bool) (t : Twist) : twistAxis (flipBy s t) = twistAxis t := by
  unfold flipBy; split
  · exact twistAxis_conj t
  · rfl

theorem flipBy_flipBy (s : Axis → Bool) (t : Twist) : flipBy s (flipBy s t) = t := by
  unfold flipBy
  by_cases h : s (twistAxis t) <;> simp [h, twistAxis_conj, QLF.Majorana.Twist.conj_conj]

/-- Every reversed reading is an involution. -/
theorem readingBy_involutive (s : Axis → Bool) (w : List Twist) :
    readingBy s (readingBy s w) = w := by
  simp [readingBy, List.map_reverse, List.map_map, Function.comp_def, flipBy_flipBy]

theorem readingBy_false (w : List Twist) : readingBy (fun _ => false) w = w.reverse := by
  have h : flipBy (fun _ => false) = id := by funext t; simp [flipBy]
  simp [readingBy, h]

theorem readingBy_true (w : List Twist) :
    readingBy (fun _ => true) w = QLF.ClosureUnitarity.dagger w := by
  have h : flipBy (fun _ => true) = Twist.conj := by funext t; simp [flipBy]
  simp [readingBy, h, QLF.ClosureUnitarity.dagger]

/-- A reading reverses handedness exactly on the axes it selects. -/
theorem handednessOn_map_flipBy (s : Axis → Bool) (a : Axis) (w : List Twist) :
    handednessOn a (w.map (flipBy s)) = if s a then - handednessOn a w else handednessOn a w := by
  induction w with
  | nil => simp [handednessOn]
  | cons t rest ih =>
    rw [List.map_cons, handednessOn_cons, handednessOn_cons, ih, twistAxis_flipBy]
    by_cases hta : twistAxis t = a
    · subst hta
      by_cases hs : s (twistAxis t)
      · simp [flipBy, hs, handedness_conj]; ring
      · simp [flipBy, hs]
    · by_cases hs : s a <;> simp [hta, hs]

theorem handednessOn_readingBy (s : Axis → Bool) (a : Axis) (w : List Twist) :
    handednessOn a (readingBy s w) = if s a then - handednessOn a w else handednessOn a w := by
  unfold readingBy
  rw [handednessOn_reverse, handednessOn_map_flipBy]

/-- **Every reversed reading maps closures onto closures.** -/
theorem readingBy_closure_iff (s : Axis → Bool) (w : List Twist) :
    countBalanced (readingBy s w) ↔ countBalanced w := by
  rw [zfa_iff_handedness_balanced, zfa_iff_handedness_balanced]
  refine forall_congr' fun a => ?_
  rw [handednessOn_readingBy]
  split <;> constructor <;> intro h <;> linarith

/-- **Every reversed reading of the census is the census.** Each closure is the reversed
    reading of a closure (its own reading), for every choice of `s`. -/
theorem every_reading_is_the_census (s : Axis → Bool) (w : List Twist) :
    countBalanced w ↔ ∃ v : List Twist, countBalanced v ∧ readingBy s v = w :=
  ⟨fun hw => ⟨readingBy s w, (readingBy_closure_iff s w).2 hw, readingBy_involutive s w⟩,
   fun ⟨v, hv, hvw⟩ => hvw ▸ (readingBy_closure_iff s v).2 hv⟩

/-- The selector named by four booleans, one per axis `I, X, Y, Z`. -/
def sel (b : Bool × Bool × Bool × Bool) : Axis → Bool
  | Axis.I => b.1
  | Axis.X => b.2.1
  | Axis.Y => b.2.2.1
  | Axis.Z => b.2.2.2

def allSelectors : List (Bool × Bool × Bool × Bool) :=
  [false, true].flatMap fun a => [false, true].flatMap fun b =>
    [false, true].flatMap fun c => [false, true].map fun d => (a, b, c, d)

/-- A closure that touches every axis. -/
def fullClosure : List Twist :=
  [Twist.up, Twist.right, Twist.slash, Twist.plus,
   Twist.down, Twist.left, Twist.backslash, Twist.minus]

theorem fullClosure_closes : countBalanced fullClosure := by
  unfold countBalanced fullClosure; decide

/-- **All sixteen reversed readings of one closure exist and are different histories**, and each
    is a closure. There is not one reversed universe but one per choice of which handedness
    components to reverse, all inside the same census. -/
theorem sixteen_reversed_readings :
    allSelectors.length = 16 ∧
      (allSelectors.map fun b => readingBy (sel b) fullClosure).Nodup ∧
      ∀ b ∈ allSelectors, countBalanced (readingBy (sel b) fullClosure) :=
  ⟨by decide, by decide, fun b _ => (readingBy_closure_iff (sel b) fullClosure).2 fullClosure_closes⟩

/-- **The selection among them is ours, and it is visible.** Closure admits every one of the
    sixteen readings, so ZFA does not choose among them; and the reading determines the choice,
    so two different selections never give the same reversed history. -/
theorem selection_identifiable :
    ∀ b ∈ allSelectors, ∀ b' ∈ allSelectors,
      readingBy (sel b) fullClosure = readingBy (sel b') fullClosure → b = b' := by
  decide

/-- **Every reversed reading has exactly one history behind it**, and the reading itself recovers
    it: if `w` is the `s`-reading of `v`, then `v` is the `s`-reading of `w`. No reversed history
    exists without the forward history it reads. -/
theorem reading_has_unique_history (s : Axis → Bool) (v w : List Twist)
    (h : readingBy s v = w) : v = readingBy s w := by
  rw [← h, readingBy_involutive]

end QLF.TimeReversalPerspective
