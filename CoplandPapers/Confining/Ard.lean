/-
Copyright (c) 2024 Paul D. Rowe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul D. Rowe
-/
import CoplandPapers.Confining.Execs

open scoped Classical
open Label
variable {E : Exec} {e : E.Evt}

/-
  This casts adv_relevant_down as having type finset. By doing so, we greatly
  simplify proofs later that rely on the finiteness, since we can rely on
  the type, giving us access to robust APIs for finite sets.
 -/
 @[simp]
noncomputable def ard (c : Component) (e : E.Evt) :=
(fin_adv_rel_down c e).toFinset

/-
  The next few lemmas extract the properties that must hold to be in ard.
-/
lemma rel_of_ard {e' : E.Evt} :
e' ∈ ard c e → Relevant c e' := by intro h; simp at h; exact h.2

lemma rel_of_ard' {e' : E.Evt} :
e' ∈ ard c e → Relevant c e' := by intro h; simp at *; exact h.2

lemma adv_lab_of_ard {e' : E.Evt} :
e' ∈ ard c e → AdvLab (E.l e') := by intro h; simp at *; exact h.1.1

lemma adv_lab_of_ard' {e' : E.Evt} :
e' ∈ ard c e → (E.l e' = cor c) ∨ (E.l e' = rep c) := by
  intro h
  have g := adv_lab_of_ard h; rw [adv_lab_adv_lab'] at g
  have g1 := rel_of_ard' h
  apply inv_relevant c e' at g1
  obtain ⟨c', g⟩ := g
  cases g1 with
  | inl g1 => tauto
  | inr g1 =>
    cases g1 with
    | inl g1 => tauto
    | inr g1 =>
      cases g1 with
      | inl g1 =>
        obtain ⟨c1, g1⟩ := g1
        rw [g1] at g; tauto
      | inr g1 =>
        cases g1 with
        | inl g1 =>
          obtain ⟨c1, g1⟩ := g1
          rw [g1] at g; tauto
        | inr g1 =>
          obtain ⟨c1, c2, ⟨g1, g2⟩⟩ := g1
          rw [g1] at g; tauto

lemma down_of_ard (e': E.Evt) : e' ∈ ard c e → e' < e := by
  intro h; simp at h; exact h.1.2

/-
  This is Lemma 1 of Confining Adversaries.

  For any given e and c, either ard c e is empty, or it has a (unique)
  maximum element.
 -/
lemma empty_or_has_max :
Relevant c e →
  (ard c e = ∅)
  ∨ (∃ e' ∈ (ard c e),
     ∀ e'' ∈ (ard c e), e'' ≤ e') := by
  intro rel
  -- Either ard c e is empty or not
  by_cases h : (ard c e = ∅)
  -- If it's empty, that's the left branch
  · left; exact h
  -- Otherwise it's the right branch
  · right
    -- We must prove there exists a maximum Evt in ard c e.
    -- Finite subsets of a partial order have maximal elements, so ard has one.
    have ne : (ard c e).Nonempty
    · rw [Finset.nonempty_iff_ne_empty]; exact h
    have m := Finset.exists_maximal (ard c e) ne
    -- Call the maximal elt of ard e'.
    obtain ⟨e', mem, m⟩ := m
    -- Then e' must be the maximum we are looking for.
    use e', mem
    -- To show it's the maximm, assume e'' is some other element of ard.
    intro e'' mem'
    -- Because e' is maximal, ¬e' < e''.
    specialize m e'' mem'
    -- Since e' ∈ ard, it is both an adversary event and Relevant to c.
    have al := adv_lab_of_ard mem
    apply rel_of_ard at mem
    -- Likewise e'' is Relevant to c.
    apply rel_of_ard at mem'
    -- Then, since E is adversary-ordered,
    have ao := E.adv_ord
    -- e' and e'' must be ordered.
    rw [← rel_relevant] at *
    specialize ao e' e'' c mem mem' al
    -- Take cases on how they are ordered.
    cases ao with
    -- If e' < e'' we get a contradiction from e' being maximal
    | inl ao => exfalso; apply m; exact ao
    -- Otherwise e'' ≤ e' as we need to show.
    | inr ao => exact le_of_lt_or_eq ao

-- Any non-empty ard has a max
lemma has_max_of_non_empty_ard :
Relevant c e → (ard c e ≠ ∅)
  → (∃ e' ∈ (ard c e), ∀ e'' ∈ (ard c e), e'' ≤ e') := by
  intro r ne
  have h := empty_or_has_max r
  cases h with
  | inl h => tauto
  | inr h => exact h

-- ard is totally ordered.
lemma ard_ordered {e1 e2: E.Evt} :
e1 ∈ ard c e → e2 ∈ ard c e →
e1 < e2 ∨ e2 < e1 ∨ e2 = e1 := by
  intro mem mem'
  have al := adv_lab_of_ard mem
  apply rel_of_ard at mem
  apply rel_of_ard at mem'
  rw [←rel_relevant] at *
  have ao := E.adv_ord; simp at ao
  exact ao e1 e2 c mem mem' al

-- Any prior corruption of c is in ard.
lemma cor_in_ard {e1 : E.Evt} :
e1 < e → (E.l e1 = cor c) → e1 ∈ ard c e := by
  intro lt lab; simp; constructor; simp
  · rw [lab]; use AdvLab.cevt;
  · apply Relevant.adv_c lab

-- Any prior repair of c is in ard.
lemma rep_in_ard {e1 : E.Evt} :
e1 < e → (E.l e1 = rep c) → e1 ∈ ard c e := by
  intro lt lab; simp; constructor; simp
  · rw [lab]; use AdvLab.revt
  · apply Relevant.adv_r lab

-- ard isn't empty if there is a prior corruption of c.
lemma ard_ne_empty_of_cor_lt {e1 : E.Evt} :
e1 < e → (E.l e1 = cor c) → ard c e ≠ ∅ := by
  intro h1 h2
  exact Finset.ne_empty_of_mem (cor_in_ard h1 h2)

-- ard isn't empty if there is a prior repair of c.
lemma ard_ne_empty_of_rep_lt {e1 : E.Evt} :
e1 < e → (E.l e1 = rep c) → ard c e ≠ ∅ := by
  intro h1 h2
  exact Finset.ne_empty_of_mem (rep_in_ard h1 h2)
