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
Exact lower bounds on `a_ZFA` (which would show a gap in Lean) are not proved here.

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

end QLF.AssemblyIndex
