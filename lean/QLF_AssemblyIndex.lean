/-
# QLF_AssemblyIndex

Stages 1 and 2 of the Lean layer for issue #264 ([`Assembly_Index_QLF.md`](../Assembly_Index_QLF.md)):
the **flat-sector assembly index** with unlimited reuse.

An *assembly pathway* is a list of twist words built one entry at a time.  Each entry is either a
primitive (a single twist, free) or the join `a ++ b` of two words already on the pathway (one
join).  Earlier entries can be reused any number of times.  `Pathway p n` says `p` is a pathway
using `n` joins.  The assembly index `assemblyIndex w` is the least `n` such that some pathway
with `n` joins contains `w`.  This is the minimum-SLP-size index of `assembly_index.py` (the
ordinary `a(x)`).

Proved here:

* `assembles_length_sub_one`: every nonempty word is assembled with `|w| − 1` joins (the left
  comb), so `assemblyIndex_le_length_sub_one`.
* `reuse_saves_a_join`: `^v^v` is assembled with 2 joins, fewer than `|w| − 1 = 3`, so reuse does
  work and the bound is not an equality.

Stage 2, the **closure-constrained** index `a_ZFA` of `assembly_index.py`: a `ClosedPathway` keeps a
*pool* of available words.  A count-balanced (closed) word stays in the pool when it is joined, so it
has unlimited reuse.  An open word is removed from the pool by the join that uses it, so it has
fan-out one.  Primitives can always be re-introduced for free.

* `closedPathway_to_pathway`: every closed-reuse pathway is simulated by an ordinary one with the
  same join count, so `assemblyIndex_le_closed`: `a(w) ≤ a_ZFA(w)`.
* `closed_assembles_length_sub_one`: the comb consumes each open prefix exactly once, so
  `a_ZFA(w) ≤ |w| − 1` too.

The census finds `a_ZFA > a` on 7.06 % of balanced words through length 10, with a maximum gap of 2.
`strict_gap_up4` (below) gives a strict gap on the unbalanced word `^^^^`; a balanced witness is open.

No axioms.  Part of [Quantum Logical Framework (QLF)](../README.md).
-/

import QLF_TwistAlphabet

namespace QLF.AssemblyIndex

open QLF

/-- A twist word. -/
abbrev Word := List Twist

/-- `Pathway p n`: `p` is an assembly pathway that uses `n` joins.  Primitives are free; a join
appends the concatenation of two words already on the pathway. -/
inductive Pathway : List Word → Nat → Prop
  | nil : Pathway [] 0
  | prim {p : List Word} {n : Nat} (t : Twist) : Pathway p n → Pathway (p ++ [[t]]) n
  | join {p : List Word} {n : Nat} {a b : Word} :
      Pathway p n → a ∈ p → b ∈ p → Pathway (p ++ [a ++ b]) (n + 1)

/-- `w` can be assembled with `n` joins. -/
def Assembles (w : Word) (n : Nat) : Prop := ∃ p, Pathway p n ∧ w ∈ p

/-- **Linear bound.**  Every nonempty word is assembled with `|w| − 1` joins. -/
theorem assembles_length_sub_one (w : Word) (hw : w ≠ []) : Assembles w (w.length - 1) := by
  induction w using List.reverseRecOn with
  | nil => exact absurd rfl hw
  | append_singleton u t ih =>
    by_cases hu : u = []
    · subst hu
      exact ⟨[[t]], by simpa using Pathway.prim t Pathway.nil, by simp⟩
    · obtain ⟨p, hp, hmem⟩ := ih hu
      have hlen : u.length ≠ 0 := by simpa [List.length_eq_zero_iff] using hu
      refine ⟨(p ++ [[t]]) ++ [u ++ [t]], ?_, by simp⟩
      have h := Pathway.join (a := u) (b := [t]) (Pathway.prim t hp)
        (List.mem_append_left _ hmem) (by simp)
      have e : u.length - 1 + 1 = (u ++ [t]).length - 1 := by simp; omega
      rw [e] at h
      exact h

/-- The set of join counts that suffice. -/
def assemblyCosts (w : Word) : Set Nat := {n | Assembles w n}

/-- The **assembly index**: the least number of joins that assembles `w` (with reuse). -/
noncomputable def assemblyIndex (w : Word) : Nat := sInf (assemblyCosts w)

/-- **`a(w) ≤ |w| − 1`** for every nonempty word. -/
theorem assemblyIndex_le_length_sub_one (w : Word) (hw : w ≠ []) :
    assemblyIndex w ≤ w.length - 1 :=
  Nat.sInf_le (assembles_length_sub_one w hw)

/-- **Reuse saves a join.**  `^v^v` is assembled with 2 joins: build `^v`, then join it to
itself.  The comb needs `|w| − 1 = 3`. -/
theorem reuse_saves_a_join :
    Assembles [Twist.up, Twist.down, Twist.up, Twist.down] 2 ∧
    assemblyIndex [Twist.up, Twist.down, Twist.up, Twist.down] <
      [Twist.up, Twist.down, Twist.up, Twist.down].length - 1 := by
  have h : Assembles [Twist.up, Twist.down, Twist.up, Twist.down] 2 := by
    have p0 := Pathway.prim Twist.down (Pathway.prim Twist.up Pathway.nil)
    have p1 := Pathway.join (a := [Twist.up]) (b := [Twist.down]) p0 (by simp) (by simp)
    have p2 := Pathway.join (a := [Twist.up, Twist.down]) (b := [Twist.up, Twist.down]) p1
      (by simp) (by simp)
    exact ⟨_, p2, by simp⟩
  refine ⟨h, ?_⟩
  have := Nat.sInf_le (s := assemblyCosts [Twist.up, Twist.down, Twist.up, Twist.down]) h
  simp only [assemblyIndex, List.length_cons, List.length_nil] at this ⊢
  omega


/-! ## Stage 2: the closure-constrained index `a_ZFA` -/

/-- `Twist` derives `BEq` alongside `DecidableEq`; the derived `==` agrees with `=`. -/
instance : LawfulBEq Twist where
  eq_of_beq {a b} h := by revert h; cases a <;> cases b <;> decide
  rfl {a} := by cases a <;> decide

instance (ts : Word) : Decidable (countBalanced ts) := by
  unfold countBalanced; infer_instance

/-- Using `x` in a join: a closed word stays available, an open word is consumed (one copy is
removed from the pool). -/
def consume (x : Word) (pool : List Word) : List Word :=
  if countBalanced x then pool else pool.erase x

theorem consume_subset (x : Word) (pool : List Word) : ∀ y ∈ consume x pool, y ∈ pool := by
  intro y hy
  unfold consume at hy
  split at hy
  · exact hy
  · exact List.mem_of_mem_erase hy

/-- `ClosedPathway pool n`: a closed-reuse assembly reaching the available pool `pool` with
`n` joins.  The second operand must still be available after the first is consumed. -/
inductive ClosedPathway : List Word → Nat → Prop
  | nil : ClosedPathway [] 0
  | prim {pool : List Word} {n : Nat} (t : Twist) :
      ClosedPathway pool n → ClosedPathway (pool ++ [[t]]) n
  | join {pool : List Word} {n : Nat} {a b : Word} :
      ClosedPathway pool n → a ∈ pool → b ∈ consume a pool →
      ClosedPathway (consume b (consume a pool) ++ [a ++ b]) (n + 1)

/-- `w` is available after a closed-reuse assembly with `n` joins. -/
def AssemblesClosed (w : Word) (n : Nat) : Prop := ∃ pool, ClosedPathway pool n ∧ w ∈ pool

/-- **Simulation.**  Every closed-reuse pathway is matched by an ordinary pathway with the same
join count whose entries include the whole pool. -/
theorem closedPathway_to_pathway {pool : List Word} {n : Nat} (h : ClosedPathway pool n) :
    ∃ p, Pathway p n ∧ ∀ y ∈ pool, y ∈ p := by
  induction h with
  | nil => exact ⟨[], Pathway.nil, fun _ hy => hy⟩
  | prim t _ ih =>
    obtain ⟨p, hp, hsub⟩ := ih
    refine ⟨p ++ [[t]], Pathway.prim t hp, fun y hy => ?_⟩
    rcases List.mem_append.1 hy with h | h
    · exact List.mem_append_left _ (hsub y h)
    · exact List.mem_append_right _ h
  | @join pool n a b _ ha hb ih =>
    obtain ⟨p, hp, hsub⟩ := ih
    have hb' : b ∈ p := hsub b (consume_subset a pool b hb)
    refine ⟨p ++ [a ++ b], Pathway.join hp (hsub a ha) hb', fun y hy => ?_⟩
    rcases List.mem_append.1 hy with h | h
    · exact List.mem_append_left _
        (hsub y (consume_subset a pool y (consume_subset b _ y h)))
    · exact List.mem_append_right _ h

theorem assemblesClosed_to_assembles {w : Word} {n : Nat} (h : AssemblesClosed w n) :
    Assembles w n := by
  obtain ⟨pool, hpool, hw⟩ := h
  obtain ⟨p, hp, hsub⟩ := closedPathway_to_pathway hpool
  exact ⟨p, hp, hsub w hw⟩

/-- The comb is also a closed-reuse pathway: each open prefix is used exactly once. -/
theorem closed_assembles_length_sub_one (w : Word) (hw : w ≠ []) :
    AssemblesClosed w (w.length - 1) := by
  induction w using List.reverseRecOn with
  | nil => exact absurd rfl hw
  | append_singleton u t ih =>
    by_cases hu : u = []
    · subst hu
      exact ⟨[[t]], by simpa using ClosedPathway.prim t ClosedPathway.nil, by simp⟩
    · obtain ⟨pool, hp, hmem⟩ := ih hu
      have hlen : u.length ≠ 0 := by simpa [List.length_eq_zero_iff] using hu
      have hp' := ClosedPathway.prim t hp
      have ha : u ∈ pool ++ [[t]] := List.mem_append_left _ hmem
      have hb : [t] ∈ consume u (pool ++ [[t]]) := by
        unfold consume
        split
        · simp
        · by_cases hut : u = [t]
          · subst hut
            -- `u = [t]` occurs twice (from `hmem` and the new primitive); one copy survives.
            rw [List.erase_append_left _ hmem]
            simp
          · rw [List.mem_erase_of_ne (Ne.symm hut)]
            simp
      have h := ClosedPathway.join hp' ha hb
      have e : u.length - 1 + 1 = (u ++ [t]).length - 1 := by simp; omega
      rw [e] at h
      exact ⟨consume [t] (consume u (pool ++ [[t]])) ++ [u ++ [t]], h,
        List.mem_append_right _ (List.mem_singleton_self _)⟩

/-- The closure-constrained assembly index `a_ZFA`. -/
noncomputable def assemblyIndexClosed (w : Word) : Nat := sInf {n | AssemblesClosed w n}

/-- `a_ZFA(w) ≤ |w| − 1`. -/
theorem assemblyIndexClosed_le_length_sub_one (w : Word) (hw : w ≠ []) :
    assemblyIndexClosed w ≤ w.length - 1 :=
  Nat.sInf_le (closed_assembles_length_sub_one w hw)

/-- **`a(w) ≤ a_ZFA(w)`.**  Restricting reuse to closed intermediates cannot lower the index. -/
theorem assemblyIndex_le_closed (w : Word) (hw : w ≠ []) :
    assemblyIndex w ≤ assemblyIndexClosed w := by
  have hne : {n | AssemblesClosed w n}.Nonempty :=
    ⟨_, closed_assembles_length_sub_one w hw⟩
  exact Nat.sInf_le (assemblesClosed_to_assembles (Nat.sInf_mem hne))


/-! ## A library of parts

Assembly can start from a **library** `L` of words already available (for example, closures made
elsewhere).  `LibPathway L pool n` is a closed-reuse pathway whose pool starts at `L` instead of
`[]`.  Library words obey the same rule: a closed one is reusable, an open one is used up once.

`libIndex_mono`: if library `L'` is contained in `L` as a multiset (`L' <+~ L`), every word costs at
most as many joins from `L` as from `L'`.  This is monotonicity, so it holds by construction and is
not evidence that diversity helps: it cannot fail for any distribution of parts.  A diversity
*advantage* would need libraries of **equal size**, one diverse and one homogeneous, and that is a
census question, not this lemma. -/

/-- Closed-reuse pathway starting from library `L`. -/
inductive LibPathway (L : List Word) : List Word → Nat → Prop
  | nil : LibPathway L L 0
  | prim {pool : List Word} {n : Nat} (t : Twist) :
      LibPathway L pool n → LibPathway L (pool ++ [[t]]) n
  | join {pool : List Word} {n : Nat} {a b : Word} :
      LibPathway L pool n → a ∈ pool → b ∈ consume a pool →
      LibPathway L (consume b (consume a pool) ++ [a ++ b]) (n + 1)

theorem consume_subperm {p q : List Word} (x : Word) (h : p.Subperm q) :
    (consume x p).Subperm (consume x q) := by
  unfold consume
  split
  · exact h
  · exact h.erase x

/-- **Simulation.**  A pathway from the smaller library is matched, join for join, by one from
the larger library whose pool contains it as a multiset. -/
theorem libPathway_mono {L' L : List Word} (hL : L'.Subperm L) {pool' : List Word} {n : Nat}
    (h : LibPathway L' pool' n) : ∃ pool, LibPathway L pool n ∧ pool'.Subperm pool := by
  induction h with
  | nil => exact ⟨L, LibPathway.nil, hL⟩
  | prim t _ ih =>
    obtain ⟨pool, hp, hs⟩ := ih
    exact ⟨pool ++ [[t]], LibPathway.prim t hp, hs.append (List.Subperm.refl _)⟩
  | @join pool' n a b _ ha hb ih =>
    obtain ⟨pool, hp, hs⟩ := ih
    have ha' : a ∈ pool := hs.subset ha
    have hb' : b ∈ consume a pool := (consume_subperm a hs).subset hb
    exact ⟨_, LibPathway.join hp ha' hb',
      (consume_subperm b (consume_subperm a hs)).append (List.Subperm.refl _)⟩

/-- `w` is available after `n` joins starting from library `L`. -/
def AssemblesFrom (L : List Word) (w : Word) (n : Nat) : Prop :=
  ∃ pool, LibPathway L pool n ∧ w ∈ pool

/-- The closure-constrained index relative to a library. -/
noncomputable def libIndex (L : List Word) (w : Word) : Nat := sInf {n | AssemblesFrom L w n}

/-- **A larger library never costs more.** -/
theorem libIndex_mono {L' L : List Word} (hL : L'.Subperm L) (w : Word)
    (hne : {n | AssemblesFrom L' w n}.Nonempty) :
    libIndex L w ≤ libIndex L' w := by
  obtain ⟨pool', hp', hw⟩ := Nat.sInf_mem hne
  obtain ⟨pool, hp, hs⟩ := libPathway_mono hL hp'
  exact Nat.sInf_le ⟨pool, hp, hs.subset hw⟩

/-- A library that already holds `w` assembles it with no joins. -/
theorem libIndex_of_mem {L : List Word} {w : Word} (hw : w ∈ L) : libIndex L w = 0 :=
  Nat.eq_zero_of_le_zero (Nat.sInf_le ⟨L, LibPathway.nil, hw⟩)


/-! ## A strict gap: `a(^^^^) = 2 < 3 = a_ZFA(^^^^)`

`^^^^` is built with two joins when reuse is free: make `^^`, then join it to itself.  Under the
closure rule `^^` is open, so it is consumed by its first use and cannot be joined to itself.  The
proof is a potential argument.  `Φ(pool)` sums `|x| − 1` over the pool's words that are nonempty
powers of `^`.  A prim adds nothing.  A join that makes a `^`-power consumes two open `^`-powers
(every nonempty `^`-power is open) and raises `Φ` by exactly one.  Any other join only removes
words.  So `Φ ≤` the number of joins, and `^^^^` in the pool forces `Φ ≥ 3`.

`^^^^` is not count-balanced.  The census's gaps are on balanced words (7.06 % through length 10);
a balanced witness is still open in Lean. -/

/-- A nonempty power of `^`. -/
def isUpPow (x : Word) : Bool := !x.isEmpty && x.all (· == Twist.up)

/-- Weight of one pool word in the potential. -/
def upWeight (x : Word) : Nat := if isUpPow x then x.length - 1 else 0

/-- The potential: the summed `upWeight` of the pool. -/
def upPotential (pool : List Word) : Nat := (pool.map upWeight).sum

theorem upPow_open {x : Word} (h : isUpPow x = true) : ¬ countBalanced x := by
  intro hc
  obtain ⟨hud, -, -, -⟩ := hc
  simp only [isUpPow, Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff,
    List.all_eq_true, beq_iff_eq] at h
  obtain ⟨hne, hall⟩ := h
  have hdown : x.count Twist.down = 0 :=
    List.count_eq_zero.2 (fun hm => by have := hall _ hm; cases this)
  have hup : 0 < x.count Twist.up := by
    obtain ⟨c, hc⟩ := List.exists_mem_of_ne_nil x hne
    have := hall c hc
    subst this
    exact List.count_pos_iff.2 hc
  omega

theorem upPotential_append (l : List Word) (y : Word) :
    upPotential (l ++ [y]) = upPotential l + upWeight y := by
  simp [upPotential]

theorem upPotential_erase {l : List Word} {x : Word} (hx : x ∈ l) :
    upPotential (l.erase x) + upWeight x = upPotential l := by
  have hp := List.perm_cons_erase hx
  unfold upPotential
  rw [(hp.map upWeight).sum_eq]
  simp [Nat.add_comm]

theorem upPotential_consume_le (x : Word) (l : List Word) :
    upPotential (consume x l) ≤ upPotential l := by
  unfold consume
  split
  · exact le_rfl
  · by_cases hx : x ∈ l
    · have := upPotential_erase hx; omega
    · rw [List.erase_of_not_mem hx]

private theorem upPow_append_left {a b : Word} (ha : a ≠ []) (h : isUpPow (a ++ b) = true) :
    isUpPow a = true := by
  simp only [isUpPow, Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff,
    List.all_eq_true, beq_iff_eq, List.mem_append] at h ⊢
  exact ⟨ha, fun c hc => h.2 c (Or.inl hc)⟩

private theorem upPow_append_right {a b : Word} (hb : b ≠ []) (h : isUpPow (a ++ b) = true) :
    isUpPow b = true := by
  simp only [isUpPow, Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff,
    List.all_eq_true, beq_iff_eq, List.mem_append] at h ⊢
  exact ⟨hb, fun c hc => h.2 c (Or.inr hc)⟩

theorem consume_of_open {x : Word} (h : ¬ countBalanced x) (l : List Word) :
    consume x l = l.erase x := by
  simp [consume, h]

/-- **The potential never exceeds the number of joins.** -/
theorem upPotential_le {pool : List Word} {n : Nat} (h : ClosedPathway pool n) :
    upPotential pool ≤ n := by
  induction h with
  | nil => simp [upPotential]
  | prim t _ ih =>
    rw [upPotential_append]
    have : upWeight [t] = 0 := by simp [upWeight]
    omega
  | @join pool n a b _ ha hb ih =>
    rw [upPotential_append]
    by_cases hab : isUpPow (a ++ b) = true
    · by_cases ha0 : a = []
      · subst ha0
        -- `[]` is count-balanced, so it is not consumed; `b` is an open `^`-power.
        have hbp : isUpPow b = true := by simpa using hab
        have hc0 : consume [] pool = pool := by
          simp [consume, countBalanced]
        rw [hc0] at hb ⊢
        rw [consume_of_open (upPow_open hbp)]
        have := upPotential_erase hb
        simp only [List.nil_append] at *
        omega
      · by_cases hb0 : b = []
        · subst hb0
          have hc0 : consume [] (consume a pool) = consume a pool := by
            simp [consume, countBalanced]
          rw [hc0]
          have hap : isUpPow a = true := by simpa using hab
          rw [consume_of_open (upPow_open hap)]
          have := upPotential_erase ha
          simp only [List.append_nil] at *
          omega
        · have hap := upPow_append_left ha0 hab
          have hbp := upPow_append_right hb0 hab
          rw [consume_of_open (upPow_open hap)] at hb ⊢
          rw [consume_of_open (upPow_open hbp)]
          have e1 := upPotential_erase ha
          have e2 := upPotential_erase hb
          have wab : upWeight (a ++ b) = a.length + b.length - 1 := by
            simp [upWeight, hab]
          have wa : upWeight a = a.length - 1 := by simp [upWeight, hap]
          have wb : upWeight b = b.length - 1 := by simp [upWeight, hbp]
          have la : 0 < a.length := List.length_pos_iff.2 ha0
          have lb : 0 < b.length := List.length_pos_iff.2 hb0
          omega
    · have : upWeight (a ++ b) = 0 := by simp [upWeight, hab]
      have h1 := upPotential_consume_le b (consume a pool)
      have h2 := upPotential_consume_le a pool
      omega

/-- The word `^^^^`. -/
def up4 : Word := [Twist.up, Twist.up, Twist.up, Twist.up]

theorem up4_needs_three {n : Nat} (h : AssemblesClosed up4 n) : 3 ≤ n := by
  obtain ⟨pool, hp, hw⟩ := h
  have e := upPotential_erase hw
  have w4 : upWeight up4 = 3 := by decide
  have := upPotential_le hp
  omega

/-- **A strict gap.**  `a(^^^^) ≤ 2` with free reuse, while `a_ZFA(^^^^) = 3`. -/
theorem strict_gap_up4 :
    assemblyIndex up4 ≤ 2 ∧ assemblyIndexClosed up4 = 3 := by
  constructor
  · apply Nat.sInf_le
    have p0 := Pathway.prim Twist.up Pathway.nil
    have p1 := Pathway.join (a := [Twist.up]) (b := [Twist.up]) p0 (by simp) (by simp)
    have p2 := Pathway.join (a := [Twist.up, Twist.up]) (b := [Twist.up, Twist.up]) p1
      (by simp) (by simp)
    exact ⟨_, p2, by simp [up4]⟩
  · have hne : {n | AssemblesClosed up4 n}.Nonempty :=
      ⟨_, closed_assembles_length_sub_one up4 (by simp [up4])⟩
    apply le_antisymm
    · have := assemblyIndexClosed_le_length_sub_one up4 (by simp [up4])
      simpa [up4] using this
    · exact up4_needs_three (Nat.sInf_mem hne)

theorem assemblyIndex_lt_closed_up4 : assemblyIndex up4 < assemblyIndexClosed up4 := by
  obtain ⟨h1, h2⟩ := strict_gap_up4
  omega

end QLF.AssemblyIndex
