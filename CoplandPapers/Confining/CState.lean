import CoplandPapers.Confining.Ard

open scoped Classical 
open Label 
variable {E : Exec} {c : Component} {e : E.Evt}

-- The type of corruption states
inductive CState : Type 
| corrupt : CState 
| regular : CState 
open CState 

-- This function produces the maximum elt of ard when we know it's nonempty. 
noncomputable def max_adv (h : Relevant c e) (h2 : ard c e ≠ ∅) : E.Evt := by 
  have m := has_max_of_non_empty_ard h h2
  use Classical.choose m 

/- 
  Useful API for working with max_adv follows
-/

-- It's actually a maximum
lemma max_of_max_adv (h : Relevant c e) (h2 : ard c e ≠ ∅) :
∀ e' ∈ ard c e, e' ≤ max_adv h h2 := by 
  intro e' h'
  have m := has_max_of_non_empty_ard h h2
  have p := (Classical.choose_spec m).2
  apply p e' h'

-- The maximum elt of ard is necessarily in ard. 
lemma max_adv_mem_ard (h : Relevant c e) (h2 : ard c e ≠ ∅) :
  (max_adv h h2) ∈ ard c e := by 
  have m := has_max_of_non_empty_ard h h2
  exact (Classical.choose_spec m).1

-- The maximum elt of ard c e is < e. 
lemma lt_of_max_adv (h : Relevant c e) (h2 : ard c e ≠ ∅): 
(max_adv h h2) < e := by 
  have g := max_adv_mem_ard h h2
  exact down_of_ard (max_adv h h2) g

-- Useful for rewriting 
lemma max_adv_def (h : Relevant c e) (h2 : ard c e ≠ ∅) {e' : E.Evt} :
  max_adv h h2 = e' ↔
  e' ∈ ard c e ∧ ∀ e'' ∈ ard c e, e'' ≤ e' := by
  constructor <;> intro h3
  · have g := max_adv_mem_ard h h2
    rw [h3] at g; use g
    intro e'' h4
    have g2 := max_of_max_adv h h2 e'' h4
    rw [h3] at g2; exact g2
  · obtain ⟨h3, h4⟩ := h3
    have m := has_max_of_non_empty_ard h h2
    have p := Classical.choose_spec m
    specialize h4 (max_adv h h2) (max_adv_mem_ard h h2)
    obtain ⟨_, p1⟩ := p
    specialize p1 e' h3
    exact le_antisymm h4 p1

-- Infer label is an adversary label. 
lemma adv_lab_of_max_adv (r : Relevant c e) (ne : ard c e ≠ ∅) :
AdvLab (E.l (max_adv r ne)) := adv_lab_of_ard (max_adv_mem_ard r ne)

-- The Component c is Relevant to max_adv. 
lemma relevant_of_max_adv (r : Relevant c e) (ne : ard c e ≠ ∅) :
Relevant c (max_adv r ne) := rel_of_ard (max_adv_mem_ard r ne)

-- max_adv is either cor c or rep c for the given c. 
lemma cor_or_rep_c_of_max_adv (r : Relevant c e) (ne : ard c e ≠ ∅) : 
E.l (max_adv r ne) = cor c ∨ E.l (max_adv r ne) = rep c := by 
  have a1 := adv_lab_of_max_adv r ne
  rw [adv_lab_adv_lab'] at a1
  obtain ⟨c1, a1⟩ := a1
  have a2 := relevant_of_max_adv r ne
  rw [←rel_relevant] at a2
  cases a1 with
  | inl a1 => 
    left
    cases a2 with 
    | meas_m c2 lab => rw [a1] at lab; cases lab
    | meas_t c2 lab => rw [a1] at lab; cases lab
    | meas_d c2 c3 lab => rw [a1] at lab; cases lab.1
    | adv_c lab => exact lab
    | adv_r lab => rw [a1] at lab; cases lab
  | inr a1 => 
    right
    cases a2 with
    | meas_m c' lab => rw [a1] at lab; cases lab
    | meas_t c' lab => rw [a1] at lab; cases lab
    | meas_d c1 c2 lab => rw [a1] at lab; cases lab.1
    | adv_c lab => rw [a1] at lab; cases lab
    | adv_r lab => exact lab

-- This is the corruption state function. 
noncomputable def cs (c : Component) : E.Evt → Option CState 
| e =>
  match (E.l e) with
  | cor c1 => dite (c1 = c) (λ _ ↦ corrupt) (λ _ ↦ none)
  | rep c1 => dite (c1 = c) (λ _ ↦ regular) (λ _ ↦ none)
  | msp _ _ => dite (Relevant c e)
      (λ (r : Relevant c e) ↦
        dite (ard c e = ∅)
        (λ (_ : ard c e = ∅) ↦ regular)
        (λ (m : ard c e ≠ ∅) ↦ 
          cs c (max_adv r m)))
      (λ _ ↦ none)
  | _ => none
termination_by e => e
decreasing_by exact lt_of_max_adv r m 

-- The above definition only applies to measurement
-- and adversary events. 
lemma meas_or_adv_of_cstate (s : CState):
cs c e = s → MSLab (E.l e) ∨ AdvLab (E.l e) := by 
  intro h; unfold cs at h
  cases' h1 : (E.l e) 
  case msp; left; constructor
  case cor; right; constructor
  case rep; right; constructor
  all_goals {dsimp at h; rw [h1] at h; cases' h}

-- If cs is defined for c at e, then c is Relevant to e
lemma relevant_of_cstate (s : CState): 
cs c e = s → Relevant c e := by 
  contrapose
  intro g h 
  unfold cs at h
  cases' h1 : (E.l e) <;> dsimp at h <;> rw [h1] at h <;> dsimp at h <;> try cases h
  case msp c1 c2
  · rw [dif_neg g] at h; cases h
  case cor c1
  · by_cases h2 : (c1 = c)
    · rw [h2] at h1; apply g
      apply Relevant.adv_c h1
    · rw [if_neg h2] at h; cases h
  case rep c1
  · by_cases h2 : (c1 = c)
    · rw [h2] at h1; apply g
      apply Relevant.adv_r h1
    · rw [if_neg h2] at h; cases h

-- If c is not Relevant to e, then cs c e is undefined. 
lemma cstate_none_of_not_relevant (r : ¬Relevant c e) : cs c e = none := by
  revert r; contrapose; push_neg; rw [Option.ne_none_iff_isSome]; intro h
  rw [Option.isSome_iff_exists] at h
  obtain ⟨a, h⟩ := h
  exact relevant_of_cstate a h

-- If c is Relevant, then cs c e is defined. 
lemma cstate_some_of_relevant (r : Relevant c e) : 
cs c e = regular ∨ cs c e = corrupt := by
  have r' := r
  rw [←rel_relevant] at r'
  have h1 := meas_cor_rep_of_relevant r
  cases r'
  case meas_m c1 lab
  · cases h1 with
    | inl h1 => 
      unfold cs; dsimp
      rw [lab]; dsimp
      rw [dif_pos r] 
      by_cases a1 : Set.Finite.toFinset (fin_adv_rel_down c e : Set.Finite (adv_relevant_down c e)) = ∅
      · left; dsimp; rw [dif_pos a1]
      · rw [dif_neg a1] 
        have a2 := cor_or_rep_c_of_max_adv r a1
        rcases a2 with a2 | a2
        all_goals{ unfold cs; dsimp; rw [a2]; simp }
    | inr h1 => 
      rcases h1 with h1 | h1
      all_goals{ rw [lab] at h1; cases h1 }
  case meas_t c1 lab
  · cases h1 with
    | inl h1 => 
      unfold cs; dsimp; rw [lab]; dsimp 
      rw [dif_pos r]; 
      by_cases a1 : Set.Finite.toFinset (fin_adv_rel_down c e : Set.Finite (adv_relevant_down c e)) = ∅
      · rw [dif_pos a1]; simp
      · rw [dif_neg a1] 
        have a2 := cor_or_rep_c_of_max_adv r a1
        rcases a2 with a2 | a2 
        all_goals{ unfold cs; dsimp; rw [a2]; simp }
    | inr h1 => 
      rcases h1 with h1 | h1
      all_goals{ rw [lab] at h1; cases h1 }
  case meas_d c1 c2 lab
  · cases h1 with
    | inl h1 => 
      unfold cs; dsimp; rw [lab.1]; dsimp 
      rw [dif_pos r]; 
      by_cases a1 : Set.Finite.toFinset (fin_adv_rel_down c e : Set.Finite (adv_relevant_down c e)) = ∅
      · rw [dif_pos a1]; simp
      · rw [dif_neg a1] 
        have a2 := cor_or_rep_c_of_max_adv r a1
        rcases a2 with a2 | a2
        all_goals{ unfold cs; dsimp; rw [a2]; simp }
    | inr h1 => 
      rcases h1 with h1 | h1
      all_goals{ rw [lab.1] at h1; cases h1 }
  case adv_c lab
  · cases h1 with
    | inl h1 =>
      rcases h1 with ⟨c1, c2, h1⟩
      rw [lab] at h1; cases h1
    | inr h1 =>
      cases h1 with 
      | inl h1 => unfold cs; dsimp; rw [lab]; simp
      | inr h1 => rw [lab] at h1; cases h1
  case adv_r lab 
  · cases h1 with
    | inl h1 => 
      rcases h1 with ⟨c1, c2, h1⟩
      rw [lab] at h1; cases h1
    | inr h1 =>
      cases h1 with 
      | inl h1 => rw [lab] at h1; cases h1
      | inr h1 => unfold cs; dsimp; rw [lab]; simp

-- If cs c e isn't corrupt then it's regular
lemma cstate_regular_of_not_corrupt (r : Relevant c e) :
¬cs c e = corrupt → cs c e = regular := by
  intro h; apply cstate_some_of_relevant at r
  rcases r with r | r 
  · exact r
  · contradiction

-- If cs c e isn't regular then it's corrupt
lemma cstate_corrupt_of_not_regular (r : Relevant c e) :
¬cs c e = regular → cs c e = corrupt := by
  intro h; apply cstate_some_of_relevant at r
  rcases r with r | r
  · contradiction
  · exact r

-- If cs c e is corrupt, then e is either a measurement
-- event or a corruption event. 
lemma cor_or_msp_of_corrupt :
  cs c e = corrupt → 
    E.l e = cor c ∨ ∃ c1 c2, E.l e = msp c1 c2 := by
  intro h
  unfold cs at h
  cases g : (E.l e)
  all_goals try {dsimp at h; rw [g] at h; dsimp at h; cases h }
  case msp c1 c2
  · right; use c1, c2
  case cor c1 
  · by_cases g1 : (c1 = c)
    · rw [g1] at *; left; rfl
    · have h1 := @relevant_of_cstate E c1 e corrupt 
      unfold cs at h1; dsimp at h1; rw [g] at h1; 
      dsimp at h1; rw [if_pos rfl] at h1; specialize h1 rfl
      cases' h1 with c2 h2 c2 h2 c2 c3 h2 c2 c3 h2
      all_goals try rw [g] at h2; cases h2 
      · contradiction
      · dsimp at h; rw [g] at h; dsimp at h;
        rw [if_neg g1] at h; contradiction
      · rw [g] at c3; contradiction
  case rep c1
  · dsimp at h; rw [g] at h; dsimp at h
    by_cases g1 : (c1 = c)
    · rw [if_pos g1] at h; cases h 
    · rw [if_neg g1] at h; contradiction

lemma ard_iff : ard c e ≠ ∅ ↔
Set.Finite.toFinset (s : Set.Finite (adv_relevant_down c e)) ≠ ∅ := by rfl

-- cs c e is the corruption state of c at the maximal
-- adversary event for c below e. 
lemma cs_max_adv_of_msp (r : Relevant c e) (h : ard c e ≠ ∅):
 (∃ c1 c2, E.l e = msp c1 c2)
  → cs c e = cs c (max_adv r h) := by
  rintro ⟨c1, c2, h1⟩; dsimp at h
  conv => 
    left 
    unfold cs; dsimp
    rw [h1]; dsimp
  rw [dif_pos r, dif_neg h]

-- If cs c e is regular, then e is either a measurement
-- event or a repair event. 
lemma rep_or_msp_of_regular :
  cs c e = regular → 
    E.l e = rep c ∨ ∃ c1 c2, E.l e = msp c1 c2 := by
  intro h
  unfold cs at h 
  cases g : (E.l e)
  all_goals try dsimp at h; rw [g] at h; dsimp at h; cases h
  case msp c1 c2
  · right; use c1, c2
  case cor c1
  · dsimp at h; rw [g] at h; dsimp at h
    by_cases g1 : (c1 = c)
    · rw [if_pos g1] at h; cases h
    · rw [if_neg g1] at h; cases h
  case rep c1
  · by_cases g1 : (c1 = c)
    · rw [g1]; left; rfl
    · unfold cs at h; dsimp at h; rw [g] at h; dsimp at h;
      rw [if_neg g1] at h
      cases h

-- A Component is corrupt at its corruption event
lemma corrupt_of_cor (h : E.l e = cor c) : cs c e  = corrupt := by 
  unfold cs; dsimp; rw [h]; dsimp; simp

-- A Component is regular at its repair event
lemma regular_of_rep (h : E.l e = rep c) : cs c e = regular := by
  unfold cs; dsimp; rw [h]; dsimp; simp

-- If a Component is corrupt, there are weakly previous
-- adversary events. 
lemma ard_nonempty_of_corrupt : cs c e = corrupt → 
ard c e ≠ ∅ ∨ (E.l e = cor c) := by 
  intro h 
  have h1 := cor_or_msp_of_corrupt h
  cases h1 with 
  | inl h1 => right; exact h1
  | inr h1 =>
    left
    have h2 := relevant_of_cstate corrupt h
    obtain ⟨c1, c2, h1⟩ := h1
    unfold cs at h; dsimp at h; rw [h1] at h; dsimp at h
    rw [dif_pos h2] at h
    by_contra h3; dsimp at h3
    rw [dif_pos h3] at h
    cases h

-- max_adv is a corruption if cs c e is corrupt. 
lemma max_adv_cor_of_corrupt (h1 : E.l e ≠ cor c) (h2 : Relevant c e) 
(h3 : ard c e ≠ ∅) (h4 : cs c e = corrupt) :
E.l (max_adv h2 h3) = cor c := by 
  have g := cor_or_msp_of_corrupt h4
  rcases g with g | g 
  · tauto
  · obtain ⟨c1, c2, g1⟩ := g
    unfold cs at h4; dsimp at h4; rw [g1] at h4; dsimp at h4
    rw [dif_pos h2] at h4
    dsimp at h3; rw [dif_neg h3] at h4
    apply cor_or_msp_of_corrupt at h4
    cases h4 with 
    | inl h4 => exact h4
    | inr h4 => 
      have mem := max_adv_mem_ard h2 h3
      have al := adv_lab_of_ard mem
      rw [adv_lab_adv_lab'] at al
      have r := rel_of_ard mem
      replace r := components_of_adv_lab r al
      cases r with 
      | inl r => exact r
      | inr r => 
        obtain ⟨c1', c2', h4⟩ := h4
        obtain ⟨c3', al⟩ := al
        cases al with 
        | inl al => rw [al] at h4; cases h4
        | inr al => rw [al] at h4; cases h4

-- max_adv is a repair if it exists and cs c e is regular. 
lemma max_adv_rep_of_regular (h1 : E.l e ≠ rep c) (h2 : Relevant c e)
(h3 : ard c e ≠ ∅) (h4 : cs c e = regular) :
  E.l (max_adv h2 h3) = rep c := by 
  have g := rep_or_msp_of_regular h4
  cases g with 
  | inl g => tauto
  | inr g => 
    obtain ⟨c1, c2, g1⟩ := g
    unfold cs at h4; dsimp at h4; rw [g1] at h4; dsimp at h4
    dsimp at h3
    rw [dif_pos h2, dif_neg h3] at h4
    apply rep_or_msp_of_regular at h4
    cases h4 with 
    | inl h4 => exact h4
    | inr h4 => 
      have mem := max_adv_mem_ard h2 h3
      have al := adv_lab_of_ard mem
      rw [adv_lab_adv_lab'] at al
      have r := components_of_adv_lab (rel_of_ard mem) al
      cases r with 
      | inl r => 
        obtain ⟨c1', c2', h4⟩ := h4
        obtain ⟨c3', al⟩ := al
        cases al with
        | inl al => rw [al] at h4; cases h4 
        | inr al => rw [al] at h4; cases h4
      | inr r => exact r

-- If cs c e is regular, then either max_adv is a 
-- repair event, or there are no prior adversary events. 
lemma ard_empty_or_max_adv_rep_of_regular (h1 : E.l e ≠ rep c) (h2 : Relevant c e)
(h3 : cs c e = regular) :
ard c e = ∅ ∨ ∃ h, E.l (max_adv h2 h) = rep c := by 
  by_cases arde : ard c e = ∅
  · tauto
  · right
    use arde; exact max_adv_rep_of_regular h1 h2 arde h3

-- If max_adv is corruption, then cs c e is corrupt. 
lemma corrupt_of_max_adv_cor (h1 : Relevant c e) 
(h2 : ard c e ≠ ∅) (h3 : E.l (max_adv h1 h2) = cor c) :
  E.l e = rep c ∨ cs c e = corrupt := by 
  by_cases eq : E.l e = rep c
  · tauto
  · right
    have := lt_of_max_adv h1 h2
    have t2 := cs_max_adv_of_msp h1 h2
    have type := meas_cor_rep_of_relevant h1
    cases type with 
    | inl type => 
      specialize t2 type; rw [t2]
      exact corrupt_of_cor h3
    | inr type => 
      cases type with 
      | inl type => exact corrupt_of_cor type
      | inr type => contradiction

-- Defines detection of corruption at a measurement event. 
def Detects' {E : Exec} (e : E.Evt) (c1 c2 : Component):=
E.l e = msp c1 c2 ∧ cs c2 e = corrupt ∧ 
∀ c, (c = c1 ∨ E.d c1 c) → cs c e = regular 

-- Defines what it means for an adversary to avoid detection
-- at an event. 
def avoids {E : Exec} (e : E.Evt) (c1 c2 : Component):= 
E.l e = msp c1 c2 ∧ cs c2 e = corrupt 
∧ ¬Detects' e c1 c2 

-- Detects predicate not relying on specific components. 
def Detects (E : Exec) (e : E.Evt) := ∃ c1 c2, Detects' e c1 c2 

-- Corruption predicate derived from cs
def Cor (E : Exec) (c : Component) (e : E.Evt) := cs c e = corrupt 

-- Useful for rewriting
lemma Cor_def {E : Exec} {c : Component} {e : E.Evt} :
Cor E c e ↔ cs c e = corrupt := by rfl

-- Defines what it means for an adversary to avoid detection
-- in an execution. 
def Avoids (E : Exec) := ∀ e : E.Evt, ¬Detects E e 
