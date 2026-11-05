import QLF_CompactLinks

/-!
# QLF_CompactBound — compact links cannot blow up, at any time step

Issue #207. The linear (non-compact) leapfrog of [`QLF_FieldEnergy`](QLF_FieldEnergy.lean) and
[`QLF_Courant`](QLF_Courant.lean) is stable only for `nτ² ≤ 1`; beyond it the field grows
exponentially. The compact leapfrog uses the Wilson force `curl(sin F)` of
[`QLF_CompactLinks`](QLF_CompactLinks.lean), and `|sin| ≤ 1` caps that force. So:

* **`force_le`.** Every component of the compact force is at most `2n` in size.
* **`E_bound`.** With currents bounded by `j`, the electric field grows at most linearly:
  `|E_m| ≤ |E_0| + m(2n|τ| + j)` at every link.
* **`A_bound`.** The link phase grows at most quadratically:
  `|A_m| ≤ |A_0| + m|τ|(|E_0| + m(2n|τ| + j))`.

These hold for **every** time step `τ`, with no Courant condition: exponential growth is impossible.
For the linear field the same statement is false (the staggered mode grows for `nτ² > 1`, computed
in [Closure_Unitarity.md](../Closure_Unitarity.md) §27). The walk's current satisfies such a bound,
`|J| ≤ Q`, its total charge (`J_sq_le` in `QLF_FieldEnergy`).

**Not here.** An exactly conserved energy for the compact leapfrog (the force is not linear, so the
argument of `QLF_FieldEnergy` does not carry over), and bounds uniform in time. No axioms.
Part of the [Quantum Logical Framework (QLF)](../README.md).
-/

namespace QLF.CompactBound

open QLF.CompactLinks Real

variable {S : Type*} [AddCommGroup S] [Fintype S] [DecidableEq S] {n : ℕ}

/-- The compact restoring force `curl(sin F)`. -/
noncomputable def force (e : Fin n → S) (a : Fin n → S → ℝ) : Fin n → S → ℝ :=
  Maxwell.curl e (sinF e a)

omit [Fintype S] [DecidableEq S] in
/-- **The compact force is bounded by `2n`.** -/
theorem force_le (e : Fin n → S) (a : Fin n → S → ℝ) (i : Fin n) (x : S) :
    |force e a i x| ≤ 2 * n := by
  unfold force Maxwell.curl sinF
  calc |∑ j, (sin (QLF.LinkAction.F e a i j x) - sin (QLF.LinkAction.F e a i j (x - e j)))|
      ≤ ∑ j, |sin (QLF.LinkAction.F e a i j x) - sin (QLF.LinkAction.F e a i j (x - e j))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin n, (2 : ℝ) := Finset.sum_le_sum fun j _ => by
        have h1 := abs_sin_le_one (QLF.LinkAction.F e a i j x)
        have h2 := abs_sin_le_one (QLF.LinkAction.F e a i j (x - e j))
        calc _ ≤ |sin (QLF.LinkAction.F e a i j x)| + |sin (QLF.LinkAction.F e a i j (x - e j))| :=
              abs_sub _ _
          _ ≤ 2 := by linarith
    _ = 2 * n := by simp; ring

/-- One step of the compact leapfrog with current `J`. -/
noncomputable def cstep (e : Fin n → S) (τ : ℝ) (J : Fin n → S → ℝ)
    (aE : (Fin n → S → ℝ) × (Fin n → S → ℝ)) : (Fin n → S → ℝ) × (Fin n → S → ℝ) :=
  let E' : Fin n → S → ℝ := fun i y => aE.2 i y + τ * force e aE.1 i y - J i y
  (fun i y => aE.1 i y - τ * E' i y, E')

/-- The compact leapfrog driven by a sequence of currents. -/
noncomputable def cevolve (e : Fin n → S) (τ : ℝ) (J : ℕ → Fin n → S → ℝ)
    (aE : (Fin n → S → ℝ) × (Fin n → S → ℝ)) : ℕ → (Fin n → S → ℝ) × (Fin n → S → ℝ)
  | 0 => aE
  | m + 1 => cstep e τ (J m) (cevolve e τ J aE m)

omit [Fintype S] [DecidableEq S] in
/-- **The electric field grows at most linearly**, for every `τ`. -/
theorem E_bound (e : Fin n → S) (τ j : ℝ) (J : ℕ → Fin n → S → ℝ) (hJ : ∀ m i x, |J m i x| ≤ j)
    (aE : (Fin n → S → ℝ) × (Fin n → S → ℝ)) (m : ℕ) (i : Fin n) (x : S) :
    |(cevolve e τ J aE m).2 i x| ≤ |aE.2 i x| + m * (2 * n * |τ| + j) := by
  induction m with
  | zero => simp [cevolve]
  | succ m ih =>
    simp only [cevolve, cstep]
    have hf := force_le e (cevolve e τ J aE m).1 i x
    have hτf : |τ * force e (cevolve e τ J aE m).1 i x| ≤ 2 * n * |τ| := by
      rw [abs_mul]; nlinarith [abs_nonneg τ]
    have hj := hJ m i x
    calc |(cevolve e τ J aE m).2 i x + τ * force e (cevolve e τ J aE m).1 i x - J m i x|
        ≤ |(cevolve e τ J aE m).2 i x| + |τ * force e (cevolve e τ J aE m).1 i x| +
            |J m i x| := by
          calc _ ≤ |(cevolve e τ J aE m).2 i x + τ * force e (cevolve e τ J aE m).1 i x| +
                |J m i x| := abs_sub _ _
            _ ≤ _ := by gcongr; exact abs_add_le _ _
      _ ≤ |aE.2 i x| + ((m + 1 : ℕ) : ℝ) * (2 * n * |τ| + j) := by push_cast; linarith

omit [Fintype S] [DecidableEq S] in
/-- **The link phase grows at most quadratically**, for every `τ`. -/
theorem A_bound (e : Fin n → S) (τ j : ℝ) (hj : 0 ≤ j) (J : ℕ → Fin n → S → ℝ)
    (hJ : ∀ m i x, |J m i x| ≤ j) (aE : (Fin n → S → ℝ) × (Fin n → S → ℝ)) (m : ℕ) (i : Fin n)
    (x : S) :
    |(cevolve e τ J aE m).1 i x| ≤
      |aE.1 i x| + m * |τ| * (|aE.2 i x| + m * (2 * n * |τ| + j)) := by
  induction m with
  | zero => simp [cevolve]
  | succ m ih =>
    have hE := E_bound e τ j J hJ aE (m + 1) i x
    simp only [cevolve, cstep] at hE ⊢
    set c : ℝ := 2 * n * |τ| + j
    have hc : 0 ≤ c := by positivity
    have hτ := abs_nonneg τ
    have h0 := abs_nonneg (aE.2 i x)
    calc |(cevolve e τ J aE m).1 i x - τ * ((cevolve e τ J aE m).2 i x +
            τ * force e (cevolve e τ J aE m).1 i x - J m i x)|
        ≤ |(cevolve e τ J aE m).1 i x| + |τ| * |(cevolve e τ J aE m).2 i x +
            τ * force e (cevolve e τ J aE m).1 i x - J m i x| := by
          rw [← abs_mul]; exact abs_sub _ _
      _ ≤ |aE.1 i x| + m * |τ| * (|aE.2 i x| + m * c) +
            |τ| * (|aE.2 i x| + ((m + 1 : ℕ) : ℝ) * c) := by gcongr
      _ ≤ |aE.1 i x| + ((m + 1 : ℕ) : ℝ) * |τ| * (|aE.2 i x| + ((m + 1 : ℕ) : ℝ) * c) := by
          push_cast
          have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
          nlinarith [mul_nonneg hτ hc, mul_nonneg (mul_nonneg hτ hc) hm]

end QLF.CompactBound
