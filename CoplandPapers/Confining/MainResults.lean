/-
Copyright (c) 2024 Paul D. Rowe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul D. Rowe
-/
import CoplandPapers.Confining.CState

open scoped Classical
open Label CState
variable {E : Exec} {c : Component} {e : E.Evt}

/-
  This is Lemma 2 of Confining Adversaries.

  If cs c e = corrupt, then either e is a corruption of c or there is a most
  recent corruption event for c before e.
-/
lemma cor_evt_of_corrupt : cs c e = corrupt → ∃ e' ≤ e, E.l e' = cor c
∧ ∀ e'' < e, (E.l e'' = cor c ∨ E.l e'' = rep c) → e'' ≤ e' := by
  intro h
  -- since the corruption state for c is defined at e, c must be Relevant to e
  have h1 := relevant_of_cstate corrupt h
  by_cases f : E.l e = cor c
  -- If E.l e = cor c, then e is the event we want.
  · use e; simp; use f
    intro e'' h3 _; exact le_of_lt h3
  -- Otherwise, E.l e ≠ cor c.
  -- Since c is corrupt at e, either ard is nonempty or e is a corruption of c
  · have h2 := ard_nonempty_of_corrupt h
    cases h2 with
    | inl h2 =>
      -- suppose ard is nonempty
      use max_adv h1 h2
      constructor
      · have h3 := lt_of_max_adv h1 h2
        exact le_of_lt h3
      · constructor
        · exact max_adv_cor_of_corrupt f h1 h2 h
        · have m1 := max_of_max_adv h1 h2
          intro e1 lt l1; specialize m1 e1
          have a1 : e1 ∈ ard c e
          · simp; constructor
            · constructor
              · cases l1 with
                | inl l1 => simp; rw [l1]; apply AdvLab.cevt
                | inr l1 => simp; rw [l1]; apply AdvLab.revt
              · exact lt
            · cases l1 with
              | inl l1 => apply Relevant.adv_c l1
              | inr l1 => apply Relevant.adv_r l1
          · exact m1 a1
    | inr h2 =>
      -- Now suppose E.l e = cor c. This contradicts the current case.
      exfalso; tauto

/-
  This is one half of Lemma 3 of Confining.
-/
lemma cor_between_regular_corrupt {e1 e2 : E.Evt} (lt : e1 < e2)
(r1 : Relevant c e1) (r2 : Relevant c e2) (cs1 : cs c e1 = regular)
(cs2 : cs c e2 = corrupt) :
∃ e', E.l e' = cor c ∧ e1 < e' ∧ e' ≤ e2 := by
  have m := inv_relevant_simp c e2 r2
  cases m with
  | inl m => use e2
  | inr m =>
    cases m with
    | inl m =>
      have cs3 := regular_of_rep m
      rw [cs2] at cs3; cases cs3
    | inr m =>
      -- We know from Lemma 2 there is some prior maximal
      -- corruption event e'.
      have h := cor_evt_of_corrupt cs2
      obtain ⟨e', h1, h2, h3⟩ := h
      -- This e' should be the one we want.
      use e'
      constructor
      -- Lemma 2 guarantees e' is a corruption of c.
      · exact h2
      -- Have to show e1 < e'.
      -- Since E is adversary-ordered,
      · have ao := E.adv_ord e' e1 c
        rw [rel_relevant, rel_relevant] at ao
        -- and since c is Relevant to e',
        have h2' := Relevant.adv_c h2
        -- e1 and e' satisfy trichotomy.
        specialize ao h2'
        specialize ao r1
        rw [h2] at ao
        specialize ao AdvLab.cevt
        -- We take cases on trichotomy
        cases ao with
        | inl ao =>
          -- if e' < e1 we derive a contradiction
          exfalso
          -- We will show that
          -- max_adv c e1 = e' = max_adv c e2.
          -- We will also show that e1 is a meas event.
          -- So cs c e1 and cs c e2 should both be
          -- cs c e'. But they differ in value, so
          -- we get a contradiction.

          -- First show e1 is a measurement event
          have msp : ∃ c1 c2, E.l e1 = msp c1 c2
          · replace r1 := inv_relevant c e1 r1
            cases r1 with
            | inl r1 =>
              apply corrupt_of_cor at r1
              rw [cs1] at r1; cases r1
            | inr r1 =>
              cases r1 with
              | inl r1 =>
                exfalso
                specialize h3 e1 lt (Or.inr r1)
                rw [lt_iff_le_and_ne] at ao
                obtain ⟨ao1, ao2⟩ := ao
                have ao3 := le_antisymm ao1 h3
                exact ao2 ao3
              | inr r1 =>
                cases r1 with
                | inl r1 => use c
                | inr r1 =>
                  cases r1 with
                  | inl r1 =>
                    obtain ⟨w, r1⟩ := r1
                    use w, c;
                  | inr r1 =>
                    obtain ⟨c1, c2, r1⟩ := r1
                    use c1, c2; exact r1.1
          -- Now we show that e' = max_adv c e1
          have g1 : e' ∈ ard c e1
          · simp; constructor;
            · simp; rw [h2]; exact ⟨AdvLab.cevt, ao⟩
            · exact h2'
          have g2 : ard c e1 ≠ ∅ := Finset.ne_empty_of_mem g1
          have g4 : ∀ e'', e'' ∈ ard c e1 → e'' ≤ e'
          · intro e'' mem'
            have lt' := down_of_ard e'' mem'
            specialize h3 e'' (lt_trans lt' lt)
            have al := adv_lab_of_ard mem'
            have rc := rel_of_ard mem'
            rw [adv_lab_adv_lab'] at al
            apply components_of_adv_lab rc at al
            exact h3 al
          -- We finally obtain e' is the maximum element
          -- of ard c e1.
          replace g1 := (max_adv_def r1 g2).2 ⟨g1, g4⟩

          -- We then need to show that e' is max_adv c e2 as well
          have f0 : e' < e2 := lt_trans ao lt
          have f1 : e' ∈ ard c e2
          · simp; constructor;
            · constructor
              · simp; rw [h2]; exact AdvLab.cevt
              · exact f0
            · exact h2'
          have f2 : ard c e2 ≠ ∅ := Finset.ne_empty_of_mem f1
          have f4 : ∀ e'', e'' ∈ ard c e2 → e'' ≤ e'
          · intro e'' mem'
            have lt' := down_of_ard e'' mem'
            specialize h3 e'' lt'
            have al := adv_lab_of_ard mem'
            have rc := rel_of_ard mem'
            rw [adv_lab_adv_lab'] at al
            apply components_of_adv_lab rc at al
            exact h3 al
          -- Finally e' is max_adv c e2
          replace f1 := (max_adv_def r2 f2).2 ⟨f1, f4⟩

          have j1 := cs_max_adv_of_msp r1 g2 msp
          have j2 := cs_max_adv_of_msp r2 f2 m
          rw [f1] at *; rw [g1] at *
          rw [←j2] at j1
          rw [cs1, cs2] at j1
          cases j1
        | inr ao =>
          cases ao with
          | inl ao =>
            -- If e1 < e' this is what we want to show.
            tauto
          | inr ao =>
            -- If e1 = e' we derive a contradiction
            exfalso
            -- corrupt = cs c e' = cs c e1 = regular.
            rw [ao] at cs1
            have cor := corrupt_of_cor h2
            rw [cs1] at *; cases cor

/-
  This is the other half of Lemma 3 of Confining.
-/
lemma rep_between_corrupt_regular {e1 e2 : E.Evt} (lt : e1 < e2)
(r1 : Relevant c e1) (r2 : Relevant c e2) (cs1 : cs c e1 = corrupt)
(cs2 : cs c e2 = regular) :
∃ e', E.l e' = rep c ∧ e1 < e' ∧ e' ≤ e2 := by
  have msp2 := inv_relevant_simp c e2 r2
  -- We first take cases on the label of e2
  cases msp2 with
  | inl msp2 =>
    -- If it's a corruption, cs c e2 will be corrupt contradicting cs2.
    apply corrupt_of_cor at msp2
    rw [cs2] at msp2; cases msp2
  | inr msp2 =>
    cases msp2 with
    | inl msp2 =>
      -- If it's a repair, then e2 is the maximal repair ≤ e2.
      use e2;
    | inr msp2 =>
      -- Otherwise the label of e2 is msp c1 c1.
      -- We will show that ard c e1 and ard c e2 are both nonempty
      -- and so each have a maximum m' and m respectively.

      -- We know from Lemma 2 that there is a maximal corruption event
      -- prior to e1. Call it e'. This will witness ard c e2 ≠ ∅.
      have h1 := cor_evt_of_corrupt cs1
      obtain ⟨e', h1, h2, _⟩ := h1
      -- We know that a must be in ard c e2,
      have a : e' ∈ ard c e2
      · simp; constructor;
        · simp
          rw [h2]
          exact ⟨AdvLab.cevt, (lt_of_le_of_lt h1 lt)⟩
        · simp; exact Relevant.adv_c h2
      -- so ard c e2 is nonempty.
      have a' : ard c e2 ≠ ∅ := Finset.ne_empty_of_mem a
      -- c is Relevant to e' because it was in ard c e2.
      have _ := rel_of_ard a
      -- Thus we can set m to be the max of ard c e2.
      set m := max_adv r2 a' with max_m
      -- This m will be the repair event between e1 and e2 we need.
      use m
      -- It's a repair event because cs c e2 is regular from it.
      have w : E.l m = rep c
      · obtain ⟨c1, c2, x⟩ := msp2
        have y : E.l e2 ≠ rep c
        · intro y; rw [x] at y; cases y
        exact max_adv_rep_of_regular y r2 a' cs2
      constructor
      · exact w
      -- It remains to show e1 < m ≤ e2
      · constructor
          -- We first show e1 < m.
          -- Since E is adversary ordered e1 and m satisfy trichotomy.
        · have ao := E.adv_ord m e1 c
          rw [rel_relevant, rel_relevant] at ao
          have h2' := Relevant.adv_r w
          specialize ao h2' r1
          rw [w] at ao
          specialize ao AdvLab.revt
          -- We take cases on trichotomy.
          cases ao with
          | inl ao =>
            -- m < e1 is the difficult case.
            exfalso
            -- First show e1 is a measurement event.
            have msp1 : ∃ c1 c2, E.l e1 = msp c1 c2
            · apply inv_relevant c e1 at r1
              cases r1 with
              | inl r1 =>
                exfalso
                have t : e1 ∈ ard c e2
                · simp;
                  constructor
                  · constructor
                    · simp; rw [r1]; exact AdvLab.cevt
                    · exact lt
                  · exact relevant_of_cstate corrupt cs1
                have t2 := max_of_max_adv r2 a'
                specialize t2 e1 t; rw [max_m] at *
                rw [lt_iff_le_and_ne] at ao
                obtain ⟨ao1, ao2⟩ := ao
                have ao3 := le_antisymm ao1 t2
                exact ao2 ao3
              | inr r1 =>
                cases r1 with
                | inl r1 =>
                  apply regular_of_rep at r1
                  rw [cs1] at r1; cases r1
                | inr r1 =>
                  cases r1 with
                  | inl r1 => use c
                  | inr r1 =>
                    cases r1 with
                    | inl r1 =>
                      obtain ⟨w, r1⟩ := r1
                      use w, c
                    | inr r1 =>
                      obtain ⟨c1, c2, r1⟩ := r1
                      use c1, c2; exact r1.1
            -- By assuming m < e1, we conclude m ∈ ard c e1.
            have ma : m ∈ ard c e1
            · simp; constructor
              · constructor
                · simp; rw [w]; exact AdvLab.revt
                · exact ao
              · exact h2'
            -- Therefore ard c e1 is nonempty,
            have ne := Finset.ne_empty_of_mem ma
            -- and has a maximum called m'.
            set m' := max_adv r1 ne with max_m'

            -- We will show that m ≤ m' and m ≤ m.
            -- e1 gets its cs value (corrupt) from m'.
            have cs3 := cs_max_adv_of_msp r1 ne msp1
            rw [cs1] at cs3

            -- Since m ∈ ard c e1 and m' is the max of that set,
            -- m ≤ m'.
            have g := max_of_max_adv r1 ne
            specialize g m ma; rw [max_m'] at *

            -- Conversely, we can show that m' ∈ ard c e2
            have j : m' ∈ ard c e2
            · simp; constructor
              · constructor
                · exact adv_lab_of_max_adv r1 ne
                · have lt' := lt_of_max_adv r1 ne
                  rw [←max_m'] at lt'; exact lt_trans lt' lt
              · exact relevant_of_max_adv r1 ne
            -- Since m' ∈ ard c e2 and m is the max of that set,
            -- m' ≤ m.
            have f := max_of_max_adv r2 a'
            specialize f m' j; rw [←max_m] at f

            -- Since they are each ≤ the other, they must be =.
            have f2 := le_antisymm g f
            -- But they differ on their cs value, giving us the
            -- contridiction we have been seeking.
            have f1 :=  cs_max_adv_of_msp r2 a' msp2
            rw [←f2] at cs3; rw [←max_m, ←cs3, cs2] at f1
            cases f1
          | inr ao =>
            -- The other two cases of trichotomy follow.
            cases ao with
            -- if e1 < m, this is what we wanted to show.
            | inl ao => exact ao
            -- if e1 = m, we derive a contradication because
            -- cs c e1 ≠ cs c m.
            | inr ao =>
              rw [ao] at cs1
              have rep := regular_of_rep w
              rw [cs1] at rep; cases rep;
        -- it is easy to show that m ≤ e2, because it's in ard c e1
        · rw [max_m]; exact le_of_lt (lt_of_max_adv r2 a')

/-
  This is Def. 6 of Confining adapted to exclude rtm.
-/
def WellSupported {E : Exec} (e : E.Evt) (c1 c2 : Component):=
  E.l e = msp c1 c2 ∧
  ∀ c, (c = c1 ∨ E.d c1 c) → ∃ e' c', E.l e' = msp c' c ∧ e' < e

/-
  This is the main theorem of Confining.
-/
theorem recent_or_deep {E : Exec} (e : E.Evt) (c1 c2 : Component)
(ws : WellSupported e c1 c2) (dnc : ∀ (e' : E.Evt) x y, ¬Detects' e' x y)
(a : avoids e c1 c2) :
(∃ c c' e' e'', D E c c2 ∧ E.l e' = msp c' c ∧ E.l e'' = cor c
  ∧ e' < e'' ∧ e'' < e) ∨
(∃ c c' e', D E c c2 ∧ D E c' c ∧ E.l e' = cor c' ∧ e' < e) := by
  -- Since the adversary avoids detection at e, c2 is corrupt at e.
  have h1 : cs c2 e = corrupt := a.2.1
  -- and by assumption 1 there is some c3 in D(c2)
  -- that is also corrupt at e.
  have h2 := a.2.2
  unfold Detects' at h2; push_neg at h2
  specialize h2 ws.1 h1;
  rcases h2 with ⟨c3, h2, h3⟩;
  have h4 : cs c3 e = corrupt;
  · unfold WellSupported at ws
    have r : Relevant c3 e
    cases h2 with
      | inl h2 => rw [←rel_relevant, h2]; exact Relev.meas_m c2 ws.1
      | inr h2 => rw [←rel_relevant]; apply Relev.meas_d c1 c2; use ws.1;
    have g := cstate_some_of_relevant r
    cases g with
    | inl g => exfalso; exact h3 g;
    | inr g => exact g
  clear h3
  have h3 : D E c3 c2; use e, c1, ws.1, h2

  -- Also, since e is well-supported, there exists e' c' s.t.
  -- E.l e' = msp c' c3 and e' < e
  have ws2 := ws.2
  specialize ws2 c3 h2
  rcases ws2 with ⟨e', c', ws2⟩
  have h5 : Relevant c3 e'
  · rw [←rel_relevant]; apply Relev.meas_t; exact ws2.1
  replace h5 := cstate_some_of_relevant h5

  -- We now take cases on cs c3 e'.
  cases h5 with
  -- If cs c3 e' = regular, we apply Lemma 3 to obtain
  -- a corruption event e'' for c3 between e' and e
  -- satisfying the first clause.
  | inl h5 =>
    have h6 := relevant_of_cstate _ h5
    have h7 : Relevant c3 e
    · rw [←rel_relevant]
      cases h2 with
      | inl h2 => apply Relev.meas_m; rw [h2]; exact ws.1
      | inr h2 => apply Relev.meas_d; use ws.1
    have t := cor_between_regular_corrupt ws2.2 h6 h7 h5 h4
    rcases t with ⟨e'', t2, t3, t4⟩
    left; use c3, c', e', e'', h3, ws2.1, t2, t3
    rw [le_iff_lt_or_eq] at t4;
    cases t4 with
    | inl t4 =>
      exact t4
    | inr t4 => subst t4; rw [ws.1] at t2; cases t2
  -- If cs c3 e' = corrupt,
  | inr h5 =>
    -- since E Detects' no corruptions,
    specialize dnc e'; unfold Detects' at dnc; push_neg at dnc
    specialize dnc c' c3 ws2.1 h5
    -- there must be some c4 s.t. D E c4 c3 corrupt at e'.
    rcases dnc with ⟨c4, h6, h7⟩;
    have h8 : cs c4 e' = corrupt
    · unfold WellSupported at ws
      have r : Relevant c4 e'
      · cases h6 with
        | inl h6 => rw [←rel_relevant]; constructor; rw [h6]; exact ws2.1
        | inr h6 => rw [←rel_relevant]; apply Relev.meas_d; use ws2.1;
      have g := cstate_some_of_relevant r
      cases g with
      | inl g => exfalso; exact h7 g
      | inr g => exact g
    clear h7
    have d : D E c4 c3; use e', c', ws2.1, h6
    -- We then apply Lemma 2 to infer there must be a
    -- corruption event e'' of c4 with e'' < e' < e satisfying
    -- clause 2.
    have h9 := cor_evt_of_corrupt h8
    rcases h9 with ⟨e'', t2, t3, _⟩
    right
    use c3, c4, e'', h3, d, t3
    exact lt_of_le_of_lt t2 ws2.2
