/-
Copyright (c) 2024 Paul D. Rowe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul D. Rowe
-/
import CoplandPapers.Confining.CState
import CoplandPapers.Lib.lib

open scoped Classical

open Label CState Function

variable (E E1 E2 : Exec)

-- This is Def. 6 of PPDP paper adapted to use dependent
-- types instead of sets.
def Enrichment {E1 E2 : Exec} (f : E1.Evt → E2.Evt) :=
(∀ e : E1.Evt, E1.l e = E2.l (f e)) ∧
(∀ {e1 e2 : E1.Evt}, e1 < e2 → (f e1) < (f e2)) ∧
(∀ e2 : E2.Evt, (∀ e1 : E1.Evt, (f e1) ≠ e2) → AdvEvt e2) ∧
(Injective f) ∧
(E1.d = E2.d)

-- The identity function is an Enrichment.
lemma enrichment_id {E : Exec} : Enrichment (id : E.Evt → E.Evt) :=
by simp [Enrichment, Injective]

-- This will define ≤ for execs.
def exec_le (E1 E2 : Exec) : Prop :=
∃ f : E1.Evt → E2.Evt, Enrichment f

-- Indeed, exec_le is reflexive and transitive
instance Exec.Preorder : Preorder Exec :=
{ le := exec_le,
  le_refl :=
    by intro E; simp; use id; exact enrichment_id
  le_trans :=
    by
      intros E1 E2 E3 h1 h2
      rcases h1 with ⟨f1, h1a, h1b, h1c⟩
      rcases h2 with ⟨f2, h2a, h2b, h2c⟩
      simp; use f2 ∘ f1; constructor
      · simp; intro e; rw [h1a e, h2a (f1 e)]
      constructor
      · simp; intro e1 e2 lt
        apply h1b at lt; exact h2b lt
      · simp; constructor
        · intros e3 im
          by_cases he2 : ∃ e2, f2 e2 = e3;
          · obtain ⟨e2, he2⟩ := he2
            have he1 : ∀ e1, f1 e1 ≠ e2
            · by_contra h
              push_neg at h; obtain ⟨e1, h⟩ := h
              rw [←h] at he2; specialize im e1
              contradiction
            replace he1 := h1c.1 e2 he1
            simp at he1
            rw [adv_lab_adv_lab'] at *; simp at he1 ⊢
            obtain ⟨c, he1⟩ := he1
            use c
            cases he1 with
            | inl he1 =>
              left; specialize h2a e2; rw [←he1]
              rw [he2] at h2a; symm; assumption
            | inr he1 =>
              right; specialize h2a e2; rw [←he1]
              rw [he2] at h2a; symm; assumption
          · push_neg at he2; exact h2c.1 e3 he2
        · use Injective.comp h2c.2.1 h1c.2.1
          rw [h1c.2.2, h2c.2.2]
}

-- API for rewriting E1 ≤ E2
lemma exec_le_def {E1 E2 : Exec} : E1 ≤ E2 ↔
∃ f : E1.Evt → E2.Evt, Enrichment f := by
  simp [LE.le, exec_le]

/-
  Since we are using Enrichment functions between types instead
  of the subset relation, we have to deal with a number of
  difficulties around inferring properties of the Enrichment
  function.
-/
lemma bijective_of_enrichment_enrichment {E1 E2 : Exec}
{f : E1.Evt → E2.Evt} {g : E2.Evt → E1.Evt}
(hf : Enrichment f) (hg : Enrichment g) : Bijective f := by
  have h1 := card_eq_of_injective hf.2.2.2.1 hg.2.2.2.1
  have h2 := (Fintype.bijective_iff_injective_and_card f).2
  exact h2 ⟨hf.2.2.2.1, h1⟩

-- Since enrichments preserve labels, they preserve
-- adversary events
lemma adv_evt_preserved {E1 E2 : Exec} {f : E1.Evt → E2.Evt}
(h : ∀ e, E1.l e = E2.l (f e)) {e : E1.Evt} (h1 : AdvEvt e) :
AdvEvt (f e) := by
  rw [adv_evt_label] at *
  obtain ⟨c, h1⟩ := h1; use c;
  cases h1 with
  | inl h1 =>
    left; rw [←h1]; symm; exact h e
  | inr h1 =>
    right; rw [←h1]; symm; exact h e

-- Enrichments also preserve relevance of components to events.
lemma relevant_preserved {E1 E2 : Exec} {f : E1.Evt → E2.Evt} (hf : Enrichment f)
{c} {e : E1.Evt} (r : Relevant c e) : Relevant c (f e) := by
  cases r with
  | meas_m c' a =>
    rw [hf.1] at a; apply Relevant.meas_m c' a
  | meas_t c' a =>
    rw [hf.1] at a; apply Relevant.meas_t c' a
  | meas_d c1 c2 a =>
    rw [hf.1, hf.2.2.2.2] at a; apply Relevant.meas_d c1 c2 a
  | adv_c r =>
    rw [hf.1] at r; apply Relevant.adv_c r
  | adv_r r =>
    rw [hf.1] at r; apply Relevant.adv_r r

-- Enrichments preserve non-emptiness of ard.
lemma ard_ne_preserved {E1 E2 : Exec} {f : E1.Evt → E2.Evt}
(hf : Enrichment f) {c} {e : E1.Evt} (r : Relevant c e)
(ane : ard c e ≠ ∅) : ard c (f e) ≠ ∅ := by
  have fmem : (f (max_adv r ane) ∈ ard c (f e))
  · simp; constructor; constructor
    · have lab : AdvLab (E1.l (max_adv r ane)) := adv_lab_of_max_adv r ane
      have aevt : AdvEvt (max_adv r ane) := by simp; exact lab
      have aevt2 : AdvEvt (f (max_adv r ane)) := adv_evt_preserved hf.1 aevt
      simp at aevt2; exact aevt2
    · exact hf.2.1 (lt_of_max_adv r ane)
    · have r' := relevant_of_max_adv r ane
      exact relevant_preserved hf r'
  apply Finset.ne_empty_of_mem fmem

/-
  The following three lemmas describe how the cardinality
  of the set of events ordered by < is affected by the
  existence of enrichments in one or both directions.
-/
lemma card_le_of_exec_le {E1 E2 : Exec}
{f1 : E1.Evt → E2.Evt} (hf1 : Enrichment f1) :
Fintype.card { p : E1.Evt × E1.Evt | p.1 < p.2 } ≤
Fintype.card { p : E2.Evt × E2.Evt | p.1 < p.2 } := by
  have f_inj := hf1.2.2.2.1
  let F := λ p : E1.Evt × E1.Evt => (f1 p.1, f1 p.2)
  have : ∀ p : E1.Evt × E1.Evt,
    p ∈ { p : E1.Evt × E1.Evt | p.1 < p.2 } →
    F p ∈ { p : E2.Evt × E2.Evt | p.1 < p.2 }
  · simp; intro e1 e2 mem; apply hf1.2.1 mem
  set F' : { p : E1.Evt × E1.Evt | p.1 < p.2 } →
           { p : E2.Evt × E2.Evt | p.1 < p.2 } :=
        λ p => ⟨F p, this p p.2⟩ with Fdef'
  have hF' : Injective F'
  · intro p1 p2 eq; rw [Fdef'] at eq; simp at eq
    ext
    apply f_inj; aesop
    apply f_inj; aesop
  apply Fintype.card_le_of_injective F' hF'

lemma card_eq_of_exec_le_le {E1 E2 : Exec}
{f1 : E1.Evt → E2.Evt} (hf1 : Enrichment f1)
{f2 : E2.Evt → E1.Evt} (hf2 : Enrichment f2) :
Fintype.card { p : E1.Evt × E1.Evt | p.1 < p.2 } =
Fintype.card { p : E2.Evt × E2.Evt | p.1 < p.2 } := by
  rw [eq_iff_le_not_lt]; constructor
  use card_le_of_exec_le hf1
  apply not_lt_of_le
  exact card_le_of_exec_le hf2

lemma card_lt_of_rel_not_surj {E1 E2 : Exec}
{f1 : E1.Evt → E2.Evt} (hf1 : Enrichment f1)
(hc : ∃ e1 e2, f1 e1 < f1 e2 ∧ ¬e1 < e2) :
Fintype.card { p : E1.Evt × E1.Evt | p.1 < p.2 } <
Fintype.card { p : E2.Evt × E2.Evt | p.1 < p.2 } := by
  have f_inj := hf1.2.2.2.1
  let F' := λ p : E1.Evt × E1.Evt => (f1 p.1, f1 p.2)
  have h1 : ∀ p, p ∈ { p : E1.Evt × E1.Evt | p.1 < p.2 } →
            (F' p) ∈ { p : E2.Evt × E2.Evt | p.1 < p.2 }
  · intro p mem; simp at mem ⊢; apply hf1.2.1 mem
  rcases hc with ⟨e1, e2, lt2, nlt1⟩
  set F : { p : E1.Evt × E1.Evt | p.1 < p.2 } →
          { p : E2.Evt × E2.Evt | p.1 < p.2 } :=
    λ p => ⟨F' p, h1 p p.2⟩ with Fdef'
  have F_inj : Injective F
  · intro p1 p2 eq; rw [Fdef'] at eq; simp at eq
    ext;
    apply f_inj; aesop
    apply f_inj; aesop
  have F_nsurj : ¬Surjective F
  · intro F_surj; unfold Surjective at F_surj
    specialize F_surj ⟨(f1 e1, f1 e2), lt2⟩
    obtain ⟨a, Feq⟩ := F_surj
    rw [Fdef'] at Feq; simp [F'] at Feq
    obtain ⟨Feq1, Feq2⟩ := Feq
    replace Feq1 := hf1.2.2.2.1 Feq1
    replace Feq2 := hf1.2.2.2.1 Feq2
    have a2 := a.2; simp at a2
    rw [Feq1, Feq2] at a2; contradiction
  apply Fintype.card_lt_of_injective_not_surjective F F_inj F_nsurj

/-
  The cardinality arguments let us infer that E1 and E2
  are isomorphic if there exist enrichments in both directions.
  That is the enrichments have inverses which are themselves
  enrichments.
-/
lemma inv_enrichment {E1 E2 : Exec}
{f1 : E1.Evt → E2.Evt} (hf1 : Enrichment f1)
{f2 : E2.Evt → E1.Evt} (hf2 : Enrichment f2)
: Enrichment (invFun f1) := by
  have bij := bijective_of_enrichment_enrichment hf1 hf2
  let fi := invFun f1
  have right_inv := rightInverse_invFun bij.2
  have bij2 : Bijective fi :=
   ⟨RightInverse.injective (rightInverse_invFun bij.2),
       LeftInverse.surjective (leftInverse_invFun bij.1)⟩
  constructor
  · intro e; specialize right_inv e
    symm; have en1 := hf1.1
    specialize en1 (invFun f1 e); rw [right_inv] at en1; rw [←en1]
  constructor
  · intro e1 e2 lt
    by_contra h
    have H1 := card_eq_of_exec_le_le hf1 hf2
    have H2 := card_lt_of_rel_not_surj hf1
    have H3 : ∃ (e1 e2 : E1.Evt), f1 e1 < f1 e2 ∧ ¬e1 < e2
    · use fi e1, fi e2; constructor
      · rw [right_inv, right_inv]; exact lt
      · exact h
    specialize H2 H3
    rw [Decidable.eq_iff_le_not_lt] at H1
    exact H1.2 H2
  constructor
  · intro e h3
    have surj := bij2.2
    specialize surj e
    obtain ⟨e2, surj⟩ := surj
    specialize h3 e2; contradiction
  constructor
  · exact RightInverse.injective right_inv
  · exact hf2.2.2.2.2

-- If E1 ≤ E2 but the strict inequality does not hold,
-- then we can show E2 ≤ E1.
lemma equiv_of_le_not_lt {E1 E2 : Exec} (le : E1 ≤ E2)
(nlt : ¬E1 < E2) : E2 ≤ E1 := by
  rw [exec_le_def] at le ⊢
  simp [LT.lt] at nlt
  exact nlt le

-- We want to show that the strict < relation on Exec is
-- well-founded. To do so, we introduce this measure function
-- into the well-founded lexicographical order on ℕ × ℕ.
noncomputable
def size (E : Exec) : ℕ × ℕ :=
(Fintype.card E.Evt, Fintype.card { p : E.Evt × E.Evt | p.1 < p.2 })

/- instance Exec.instWellFoundedRelation : WellFoundedRelation Exec := by
  apply invImage size
  exact Prod.instWellFoundedRelationProd
 -/

-- Our measure function ensures that the measure strictly
-- decreases when execs strictly decrease.
lemma size_lt_of_lt : ∀ {E1 E2}, E1 < E2 →
(size E1) < (size E2) := by
  intro E1 E2 lt
  rw [lt_iff_le_not_le] at lt
  rw [exec_le_def] at lt; cases' lt with le nle
  rcases le with ⟨f, hf⟩
  by_cases sj : Surjective f
  · simp [size]; right
    constructor
    · have bij : Bijective f := ⟨hf.2.2.2.1, sj⟩
      have eqv : Nonempty (E1.Evt ≃ E2.Evt)
      · constructor
        fconstructor
        · exact f
        · exact invFun f
        · exact leftInverse_invFun bij.1
        · exact rightInverse_invFun bij.2
      rw [le_iff_lt_or_eq]
      exact Or.inr (Fintype.card_eq.2 eqv)
    · have cle := card_le_of_exec_le hf
      rw [lt_iff_le_and_ne]; use cle; clear cle
      intro eq
      have hinv : Enrichment (invFun f)
      · constructor
        · intro e; symm
          rw [hf.1 (invFun f e), (rightInverse_invFun sj)]
        constructor
        · have clt := card_lt_of_rel_not_surj hf
          intro e1 e2 lt; by_contra h
          cases' (sj e1) with a1 ha1
          cases' (sj e2) with a2 ha2
          rw [←ha1, ←ha2] at lt h
          rw [leftInverse_invFun hf.2.2.2.1] at h
          rw [leftInverse_invFun hf.2.2.2.1] at h
          specialize clt ⟨a1, a2, lt, h⟩
          rw [lt_iff_le_and_ne] at clt
          exact clt.2 eq
        constructor
        · intro e2 hadv
          specialize hadv (f e2)
          rw [leftInverse_invFun hf.2.2.2.1] at hadv
          contradiction
        constructor
        · intro e1 e2 eq
          apply_fun f at eq
          rw [(rightInverse_invFun sj), (rightInverse_invFun sj)] at eq
          exact eq
        · symm; exact hf.2.2.2.2
      exact nle ⟨(invFun f), hinv⟩
  · simp [size]; left
    constructor
    · apply Fintype.card_lt_of_injective_not_surjective f hf.2.2.2.1 sj
    · exact card_le_of_exec_le hf

-- < is a well-founded relation on Exec.
lemma Exec.lt_wf : WellFounded (LT.lt : Exec → Exec → Prop) := by
  apply Subrelation.wf size_lt_of_lt
  apply InvImage.wf
  exact wellFounded_lt

-- A query is a dependent pair consisting of an Exec
-- together with a corruption predicate over components
-- and events of that Exec.
def Query := Σ (E : Exec), Component → E.Evt → Prop

-- We define ≤ on queries to hold iff their execs are ≤ and
-- furthermore the Enrichment witnessing ≤ for execs preserves
-- the corruption predicate.
def QueryLE (q1 q2 : Query) :=
  ∃ (f : q1.1.Evt → q2.1.Evt),
    Enrichment f ∧ ∀ c e1, q1.2 c e1 → q2.2 c (f e1)

-- Queries form a preorder under QueryLE.
instance Query.preorder : Preorder Query :=
{ le := QueryLE,
  le_refl := by
    intro a; use id
    constructor
    · constructor
      · simp
      constructor
      · simp
      · simp; exact injective_id
    · simp
  le_trans := by
    intro a b c lt1 lt2
    rcases lt1 with ⟨f1, ⟨h1a, h1b, h1c⟩, h1d⟩
    rcases lt2 with ⟨f2, ⟨h2a, h2b, h2c⟩, h2d⟩
    use (f2 ∘ f1)
    constructor
    · constructor
      · simp; intro e; rw [h1a e, h2a (f1 e)]
      · constructor
        · simp; intro e1 e2 lt
          replace lt := h1b lt; exact h2b lt
        · simp
          constructor
          · intros e3 im
            by_cases he2 : ∃ e2, f2 e2 = e3
            · obtain ⟨e2, he2⟩ := he2
              have he1 : ∀ e1, f1 e1 ≠ e2
              · by_contra h
                push_neg at h; obtain ⟨e1, h⟩ := h
                rw [←h] at he2; specialize im e1
                contradiction
              replace he1 := h1c.1 e2 he1
              simp at he1
              rw [adv_lab_adv_lab'] at *; simp at he1 ⊢
              obtain ⟨c, he1⟩ := he1
              use c;
              cases he1 with
              | inl he1 =>
                left; specialize h2a e2; rw [←he1]
                rw [he2] at h2a; symm; assumption
              | inr he1 =>
                right; specialize h2a e2; rw [←he1]
                rw [he2] at h2a; symm; assumption
            · push_neg at he2; exact h2c.1 e3 he2
          · use Injective.comp h2c.2.1 h1c.2.1
            rw [h1c.2.2, h2c.2.2]
    · intro c1 e1 p1; simp
      apply h2d c1 (f1 e1)
      apply h1d c1 e1 p1
}

-- API for rewriting ≤ on queries.
lemma query_le_def {q1 q2 : Query} : q1 ≤ q2 ↔
∃ f : q1.1.Evt → q2.1.Evt, Enrichment f ∧
∀ (c : Component) (e1 : q1.1.Evt), q1.2 c e1 → q2.2 c (f e1) := by
  simp [LE.le, QueryLE]

-- If queries are related by ≤, so are their execs.
lemma exec_le_of_query_le {q1 q2 : Query} :
q1 ≤ q2 → q1.1 ≤ q2.1 := by
  intro h
  rcases h with ⟨f, h1, _⟩
  use f

-- Defines "agreement" of the corruption predicates on
-- corresponding arguments.
def query_cor_agree {q1 q2 : Query} {f : q1.1.Evt → q2.1.Evt}
(_ : Enrichment f) (c : Component) (e : q1.1.Evt) :=
  q1.2 c e = q2.2 c (f e)

-- If two queries are related by a strict inequality, then
-- either their execs are so related, or their corruption
-- predicates are.
lemma cor_lt_of_query_lt_exec_nlt {q1 q2 : Query} (lt : q1 < q2)
{f : q1.1.Evt → q2.1.Evt} (hf : Enrichment f) :
q1.1 < q2.1 ∨
∃ (_ : q1.1 ≤ q2.1) (c : Component) (e : q1.1.Evt), ¬query_cor_agree hf c e := by
  by_cases h : (q1.1 < q2.1)
  · left; exact h
  · right; have le := le_of_lt lt
    rw [query_le_def] at le
    have h1 : q1.1 ≤ q2.1 := ⟨f, hf⟩
    use h1
    have nle := lt.2
    simp [QueryLE] at nle
    have h3 := equiv_of_le_not_lt h1 h
    let f1 := invFun f
    have h5 : Enrichment f1
    · obtain ⟨f2, hf2⟩ := h3
      exact inv_enrichment hf hf2
    specialize nle f1 h5
    rcases nle with ⟨c, e, g1, g2⟩
    use c, f1 e
    unfold query_cor_agree
    have eq : (f (f1 e)) = e
    · have bij := bijective_of_enrichment_enrichment hf h5
      rw [rightInverse_invFun bij.2]
    rw [eq]; simp
    rintro ⟨_, g4⟩
    specialize g4 g1; exact g2 g4

-- Definition 8 of PPDP.
def denotation (q : Query) : Set Exec :=
  { E' : Exec | q ≤ ⟨E', (Cor E')⟩ ∧ ∀ e, ¬Detects E' e }

notation "⟪" q "⟫" => denotation q

-- Definition 9 of PPDP.
def Saturated (q : Query) :=
  (∀ c e, q.2 c e ↔ Cor q.1 c e) ∧ (∀ e, ¬Detects q.1 e)

-- Lemma 10 of the PPDP paper.
lemma in_denotation_of_saturated {q : Query} (s : Saturated q) :
q.1 ∈ ⟪ q ⟫ := by
  constructor
  · use id; simp; use enrichment_id
    intro c1 e1 p1
    --unfold Saturated at s
    obtain ⟨s1, _⟩ := s
    exact (s1 c1 e1).1 p1
  · intro e
    unfold Saturated at s
    unfold Detects at *; push_neg
    intro c1 c2
    obtain ⟨_, s2⟩ := s
    specialize s2 e
    push_neg at s2
    exact s2 c1 c2

/-
  We develop cardinality results for queries analogous to
  those for execs to reason about what is possible when
  queries are related by <.
-/
lemma query_cor_card_le {q1 q2 : Query}
{f : q1.1.Evt → q2.1.Evt} (hf : Enrichment f)
(cpf : ∀ c e, q1.2 c e → q2.2 c (f e))
{c : Component}
{A : Set q1.1.Evt} {B : Set q2.1.Evt}
(hA : A = { e | q1.2 c e})
(hB : B = { e | q2.2 c e}) :
Fintype.card A ≤ Fintype.card B := by
  rw [hA, hB]
  have f_inj := hf.2.2.2.1
  have fset : ∀ e, e ∈ { e | q1.2 c e} → f e ∈ { e | q2.2 c e}
  · intro e mem; simp at mem
    simp; exact cpf c e mem
  set F' : { e | q1.2 c e} → { e | q2.2 c e} :=
    λ e => ⟨f e, fset e e.2⟩ with Fdef'
  have F_inj' : Injective F'
  · intro e1 e2 eq; rw [Fdef'] at eq; simp at eq
    ext; apply f_inj; tauto
  apply Fintype.card_le_of_injective F' F_inj'

lemma query_cor_card_eq {q1 q2 : Query}
{f : q1.1.Evt → q2.1.Evt} (hf : Enrichment f)
{g : q2.1.Evt → q1.1.Evt} (hg : Enrichment g)
(c : Component)
(cpf : ∀ c e, q1.2 c e → q2.2 c (f e))
(cpg : ∀ c e, q2.2 c e → q1.2 c (g e))
{A : Set q1.1.Evt} {B : Set q2.1.Evt}
(hA : A = { e | q1.2 c e})
(hB : B = { e | q2.2 c e}) :
Fintype.card A = Fintype.card B := by
  have AleB := query_cor_card_le hf cpf hA hB
  have BleA := query_cor_card_le hg cpg hB hA
  rw [eq_iff_le_not_lt]
  use AleB
  apply not_lt_of_le
  exact BleA

lemma query_cor_card_lt {q1 q2 : Query}
{f : q1.1.Evt → q2.1.Evt} (hf : Enrichment f)
(cpf : ∀ c e, q1.2 c e → q2.2 c (f e))
{A : Set q1.1.Evt} {B : Set q2.1.Evt} (c : Component)
(hA : A = { e | q1.2 c e}) (hB : B = { e | q2.2 c e})
(ns : ∃ e, ¬q1.2 c e ∧ q2.2 c (f e)) :
Fintype.card A < Fintype.card B := by
  rw [hA, hB]
  have h1 : ∀ e, e ∈ { e | q1.2 c e} → (f e) ∈ { e | q2.2 c e}
  · intro e; simp; exact cpf c e
  rcases ns with ⟨e, np1, p2⟩
  set F : { e | q1.2 c e} → { e | q2.2 c e} := λ e => ⟨f e, h1 e e.2⟩ with hF
  have F_inj : Injective F
  · intro e1 e2 Feq; rw [hF] at Feq; simp at Feq
    ext; exact hf.2.2.2.1 Feq
  have F_nsurj : ¬Surjective F
  · intro F_surj;
    specialize F_surj ⟨(f e), p2⟩
    obtain ⟨a, Feq⟩ := F_surj
    rw [hF] at Feq; simp at Feq
    replace Feq := hf.2.2.2.1 Feq
    have a2 := a.2; simp at a2
    rw [Feq] at a2; contradiction
  apply Fintype.card_lt_of_injective_not_surjective F F_inj F_nsurj

-- Lemma 11 of the PPDP paper.
lemma not_denoted_by_of_saturated_lt {q1 q2: Query}
(s : Saturated q1) (lt : q1 < q2) : q1.1 ∉ ⟪ q2 ⟫ := by
  by_cases h : q1.1 < q2.1
  · by_contra h1
    unfold denotation at h1; simp at h1
    obtain ⟨h1, h2⟩ := h1
    replace h := not_le_of_lt h
    rw [query_le_def] at h1
    rw [exec_le_def] at h
    push_neg at h
    obtain ⟨f, h1⟩ := h1
    specialize h f
    exact h h1.1
  · -- Since E is not strictly < E', we must have
    -- E ≤ E' and E' ≤ E.
    rintro ⟨⟨g, hg, cpg'⟩, _⟩
    rcases (le_of_lt lt) with ⟨f, hf, cpf⟩
    have cpg : ∀ c e, q2.2 c e → q1.2 c (g e)
    · intro c e p2; specialize cpg' c e; simp at cpg'
      obtain ⟨s1, _⟩ := s; rw [←s1 c (g e)] at cpg'; tauto
    -- we now have f : E → E' and g : E' → E, both
    -- are enrichments. We know they each have inverses
    -- that are also enrichments. Which do we want to
    -- use to talk about the "same" elements of E/E'?
    -- We will need g's corruption preserving properties
    -- later, so let's use g.
    have gbij := bijective_of_enrichment_enrichment hg hf
    have hg_inv := inv_enrichment hg hf
    -- Ok, so we know that (invFun f) is also an Enrichment.

    have Hg : ∀ c e, q2.2 c e ↔ q1.2 c (g e)
    · intro c e; constructor
      · exact cpg c e
      · intro p1; by_contra h
        have ns : ∃ e, ¬q2.2 c e ∧ Cor q1.1 c (g e)
        · use e; rw [s.1 c (g e)] at p1
          exact ⟨h, p1⟩
        set A := { e | q1.2 c e } with hA
        set B := { e | q2.2 c e } with hB
        set A' := { e | Cor q1.1 c e } with hA'
        have Aeq : A = A'
        · ext x; rw [hA, hA']
          simp; exact s.1 c x
        have ceq := query_cor_card_eq hf hg c cpf cpg hA hB
        have clt := query_cor_card_lt hg cpg' c hB hA' ns
        rw [lt_iff_le_not_le] at clt
        rw [eq_iff_le_not_lt] at ceq
        rw [←Aeq] at clt
        exact clt.2 ceq.1
    have Hg' : ∀ c e, q1.2 c e ↔ q2.2 c (invFun g e)
    · intro c e
      have he : e = g ((invFun g) e)
      · rw [rightInverse_invFun gbij.2]
      specialize Hg c (invFun g e)
      constructor
      · intro pp1; rw [he] at pp1
        exact Hg.2 pp1
      · intro pp2; rw [he]
        exact Hg.1 pp2

    -- "In the other case, where φ < φ', there is some
    -- (c,e) such that ¬φ(c, e), but φ'(c, e)."
    have H1 : ∃ c e, q2.2 c (invFun g e) ∧ ¬ q1.2 c e
    · have H1 := cor_lt_of_query_lt_exec_nlt lt hg_inv
      have H2 := cor_lt_of_query_lt_exec_nlt lt hf
      cases H1 with
      | inl H1 =>
        contradiction
      | inr H1 =>
        rcases H1 with ⟨_, Hc, He, H4⟩
        unfold query_cor_agree at H4
        use Hc, He
        specialize cpf Hc He
        specialize cpg Hc (invFun g He)
        simp at H4
        by_cases H5 : q1.2 Hc He
        · specialize Hg' Hc He; tauto
        · tauto
    -- By Def. 8 (denotation), condition (b), for every
    -- element E'' ∈ ⟪q2⟫, Cor E'' c e holds. In particular,
    -- since we are taking E ∈ ⟪q2⟫ and deriving a contradiction,
    -- we must show that Cor E c e holds. But e in this case
    -- is really (f e), so we really need to show that
    -- Cor E c (f⁻¹ (f e)) holds.
    rcases H1 with ⟨c, e, p2, np1⟩
    have cor : Cor q1.1 c (g ((invFun g) e))
    · apply cpg'; exact p2
    rw [rightInverse_invFun gbij.2] at cor
    cases' s with s1 s2
    specialize s1 c e; rw [←s1] at cor
    exact np1 cor

-- Definies the set of minimal elements for a set of queries.
def minimize (S : Set Query) :=
  minimals QueryLE S

-- This is R as defined in the statement of Theorem 12 of PPDP.
def R (q : Query) : Set Query := { q' | q ≤ q' ∧ Saturated q' }

-- Simple observation that all elts of R q are Saturated.
lemma R_saturated (q : Query) : ∀ q' ∈ R q, Saturated q' := by
  intro q' mem; exact mem.2

/-
  The proof of Theorem 12 relies essentially on the fact that
  we can always find minimal elements of R q below any given
  element. That requires < to be well-founded on R q. In fact,
  < is well-founded on the set of all Saturated queries. To
  prove that, we reduce to the well-foundedness of execs.
  We can do this because, for Saturated queries, q1 < q2
  implies that q1.1 < q2.1. So we can adapt the measure function
  for showing well-foundedness of execs above.
-/
lemma exec_lt_of_saturated_query_lt {q1 q2 : Query}
(qlt : q1 < q2) (s1 : Saturated q1) (s2 : Saturated q2) :
q1.1 < q2.1 := by
  rw [lt_iff_le_not_le] at qlt ⊢
  obtain ⟨qlt1, qlt2⟩ := qlt
  rw [query_le_def] at qlt1
  rcases qlt1 with ⟨f, hf, _⟩
  constructor
  · rw [exec_le_def]
    exact ⟨f, hf⟩
  · intro le
    suffices : q2 ≤ q1; exact qlt2 this
    rw [query_le_def]
    obtain ⟨g, hg⟩ := le
    use g, hg
    intro c e p2; by_contra np1
    have bij := bijective_of_enrichment_enrichment hg hf
    have ie := inv_enrichment hg hf
    rw [(s2.1 c e), Cor_def] at p2
    rw [(s1.1 c (g e)), Cor_def] at np1
    have r2 := relevant_of_cstate _ p2
    have r1 := relevant_preserved hg r2
    have p1 := cstate_regular_of_not_corrupt r1 np1
    clear np1
    have lab := rep_or_msp_of_regular p1
    cases lab with
    | inl lab =>
      have clab := cor_or_msp_of_corrupt p2
      cases clab with
      | inl clab =>
        rw [hg.1, lab] at clab; cases clab
      | inr clab =>
        rcases clab with ⟨c1, c2, mlab⟩
        rw [hg.1, lab] at mlab; cases mlab
    | inr lab =>
      rcases lab with ⟨c1, c2, mlab⟩
      have nlrep1 : q1.1.l (g e) ≠ rep c
      · intro lrep; rw [mlab] at lrep; cases lrep
      have nlcor2 : q2.1.l e ≠ cor c
      · intro lcor; rw [hg.1, mlab] at lcor; cases lcor
      have ane2 := ard_nonempty_of_corrupt p2
      have h1 := ard_empty_or_max_adv_rep_of_regular nlrep1 r1 p1
      cases h1 with
      | inl h1 =>
        cases ane2 with
        | inl ane2 => exact (ard_ne_preserved hg r2 ane2) h1
        | inr ane2 => rw [hg.1, mlab] at ane2; cases ane2
      | inr h1 =>
        cases ane2 with
        | inr ane2 => exact nlcor2 ane2
        | inl ane2 =>
          obtain ⟨ane1, h2⟩ := h1
          set m2 := (invFun g) (max_adv r1 ane1) with hm2
          have m2_rep : q2.1.l m2 = rep c
          · rw [ie.1 (max_adv r1 ane1)] at h2
            have ane2 := ard_ne_preserved ie r1 ane1
            rw [leftInverse_invFun bij.1] at ane2
            have : (invFun g) (max_adv r1 ane1) < (max_adv r2 ane2)
            · have hx1 := lt_of_max_adv r1 ane1
              replace hx1 := ie.2.1 hx1
              rw [leftInverse_invFun bij.1] at hx1
              have mina : (invFun g) (max_adv r1 ane1) ∈ ard c e
              · exact rep_in_ard hx1 h2
              have max := max_of_max_adv r2 ane2
              specialize max _ mina
              rw [le_iff_lt_or_eq] at max
              cases max with
              | inl max => tauto
              | inr max =>
                apply_fun q2.1.l at max; rw [h2] at max
                have ncor : q2.1.l e ≠ cor c
                · intro clab; rw [hg.1, mlab] at clab; cases clab
                have mcor := max_adv_cor_of_corrupt ncor r2 ane2 p2
                rw [mcor] at max; cases max
            rw [←hm2] at h2; exact h2
          have m2_lt : m2 < e
          · have glt : g m2 < g e
            · rw [hm2, rightInverse_invFun bij.2]
              exact lt_of_max_adv r1 ane1
            replace glt := ie.2.1 glt
            rw [leftInverse_invFun bij.1, leftInverse_invFun bij.1] at glt
            exact glt
          have m2_ia :=rep_in_ard m2_lt m2_rep
          have max := max_of_max_adv r2 ane2
          specialize max m2 m2_ia
          rw [le_iff_lt_or_eq] at max
          cases max with
          | inr max =>
            have m2_cor := max_adv_cor_of_corrupt nlcor2 r2 ane2 p2
            rw [←max, m2_rep] at m2_cor; cases m2_cor
          | inl max =>
            have max_lt := lt_of_max_adv r2 ane2
            replace max := hg.2.1 max
            replace max_lt := hg.2.1 max_lt
            rw [hm2, rightInverse_invFun bij.2] at max
            have m2_ard : g (max_adv r2 ane2) ∈ ard c (g e)
            · have rc := cor_or_rep_c_of_max_adv r2 ane2
              cases rc with
              | inl rc => rw [hg.1] at rc; exact cor_in_ard max_lt rc
              | inr rc => rw [hg.1] at rc; exact rep_in_ard max_lt rc
            have max1 := max_of_max_adv r1 ane1 (g (max_adv r2 ane2)) m2_ard
            replace max := not_le_of_lt max
            exact max max1

-- The adapted measure function for queries.
noncomputable
def qsize (q : Query) := size q.1

-- Restricting it to Saturated queries
noncomputable
def qsize' (q : ↥{q : Query | Saturated q}) := size q.val.1

/- instance Query.instWellFoundedRelation : WellFoundedRelation Query := by
  apply invImage qsize
  exact Prod.instWellFoundedRelationProd

instance SaturatedQuery.instWellFoundedRelation :
WellFoundedRelation ↥{q : Query | Saturated q} := by
  apply invImage qsize'
  exact Prod.instWellFoundedRelationProd -/


-- This measure function has the property that strict reduction
-- in queries results in strict reduction in the measure.
lemma qsize_lt_of_lt {q1 q2 : Query} (s1 : Saturated q1)
(s2 : Saturated q2) (lt : q1 < q2)  :
--(Prod.lex Nat.lt_wfRel Nat.lt_wfRel).rel (qsize q1) (qsize q2) := by
(qsize q1) < (qsize q2) := by
  replace lt := exec_lt_of_saturated_query_lt lt s1 s2
  unfold qsize
  apply size_lt_of_lt lt

-- Indeed, < is a well-founded relation on the set of
-- Saturated queries.
lemma saturated_query_wf :
Set.WellFoundedOn { q : Query | Saturated q} (LT.lt : Query → Query → Prop) := by
  unfold Set.WellFoundedOn
  apply Subrelation.wf _
  apply InvImage.wf; use qsize'
  swap
  exact LT.lt
  exact wellFounded_lt
  intro x y lt
  exact qsize_lt_of_lt x.2 y.2 lt

-- This is the key fact used in the proof of Theorem 12 below.
-- It states the existence of a minimal member of R q (weakly)
-- below any given member.
lemma min_covers (q : Query) {q'} (mem : q' ∈ R q) :
∃ qm ∈ minimize (R q), qm ≤ q' := by
  have swf : (R q).IsWF
  · apply Set.WellFoundedOn.subset saturated_query_wf
    intro x hx; simp; exact (R_saturated q) x hx
  set leq' := { x ∈ (R q) | x ≤ q'} with hl
  have lqwf : leq'.IsWF
  · apply Set.WellFoundedOn.subset swf
    intro x hx; exact hx.1
  have mem' : q' ∈ leq'; rw [hl]; simp [R] at mem ⊢; tauto
  have ne : leq'.Nonempty := Set.nonempty_of_mem mem'
  set qm := Set.IsWF.min lqwf ne with hqm
  have qm_min := Set.IsWF.min_mem lqwf ne
  have qmle : qm ≤ q'
  · simp at qm_min
    rw [hqm]; exact qm_min.2
  use qm; constructor
  · unfold minimize; unfold minimals; simp
    constructor
    · simp at qm_min; rw [←hqm] at qm_min; exact qm_min.1
    · intro b bmem le
      have bleq : b ∈ leq'
      · use bmem; exact le_trans le qmle
      have bnlt := Set.IsWF.not_lt_min lqwf ne bleq
      by_contra h
      change b ≤ qm at le
      have lt := lt_of_le_not_le le h
      exact bnlt lt
  · exact qmle

-- Since R q only contains things denoted by q, all elements
-- are at least as great as q itself.
lemma lt_rmin (q : Query) : ∀ q' ∈ minimize (R q), q ≤ q' := by
  intro q' rmin; simp [minimize, R] at rmin
  exact rmin.1.1

-- Theorem 12 of PPDP
theorem denotation_eq_denotation_rmin (q : Query) :
⟪ q ⟫ = ⋃ (q' : minimize (R q)), ⟪ q' ⟫ := by
  ext E'
  constructor <;> intro mem
  · obtain ⟨le, ndet⟩ := mem
    simp
    -- By Def. 8, q.1 ≤ E' (⟨f, hf⟩), q.2 ≤ Cor E' (cpf),
    -- and ∀ e, ¬Detects E' e (ndet)
    have s : Saturated ⟨E', Cor E'⟩
    · unfold Saturated; tauto
    have rmem : (⟨E', Cor E'⟩ : Query) ∈ (R q) := Set.mem_sep le s
    rcases min_covers q rmem with ⟨qm, den, mle⟩
    use qm, den
    simp [denotation]
    exact ⟨mle, ndet⟩
  · simp at mem
    rcases mem with ⟨q', qmin, den⟩
    replace qmin := lt_rmin q q' qmin
    unfold denotation at *; simp at *
    apply And.intro _ den.2
    exact le_trans qmin den.1

/-
  A Suitable query is one in which the corruption predicate
  always designates corruption events as corrupt, it never
  designates repair events as corrupt, and it never designates
  a Component corrupt at an event to which it is not Relevant.
  The PPDP paper does not use this, and is technically incorrect
  as a result. The proofs implicitly assume that we have
  restricted to such queries in Theorem 16.
-/
def Suitable (q : Query) : Prop :=
  ∀ c e,
    (q.1.l e = cor c → q.2 c e) ∧
    (q.1.l e = rep c → ¬q.2 c e) ∧
    (q.2 c e → Relevant c e)

/-
  This corresponds to Theorem 16 of PPDP. The theorem as stated
  in PPDP is not correct. This version fixes it. First, it
  explicitly restricts attention to Suitable queries. Second,
  formulas 2 and 3 have been modified to add a disjunct
  accounting for the fact that the event could be a corruption
  event.
-/
theorem saturated_iff (q : Query) (R : Suitable q) :
Saturated q ↔
(∀ e c1 c2, q.1.l e = msp c1 c2 → q.2 c2 e →
  q.2 c1 e ∨ ∃ c3, q.1.d c1 c3 ∧ q.2 c3 e) ∧
(∀ e c, q.2 c e →
  q.1.l e = cor c ∨ ∃ e', e' < e ∧ q.1.l e' = cor c) ∧
(∀ e1 e2 c, e1 < e2 → q.2 c e2 → q.1.l e1 = rep c →
  q.1.l e2 = cor c ∨ ∃ e', e1 < e' ∧ e' < e2 ∧ q.1.l e' = cor c) ∧
(∀ e1 e2 c, e1 < e2 → q.1.l e1 = cor c → MeasEvt e2 →
  Relevant c e2 → q.2 c e2 ∨ ∃ e', e1 < e' ∧ e' < e2 ∧
  q.1.l e' = rep c) := by
  constructor
  · --contrapose, intro h, push_neg at h,
    intro s
    -- separate into cases and order them properly
    constructor; swap; constructor; swap; constructor; pick_goal 3; pick_goal 4
    -- Formula 1
    · intro e c1 c2 lab p2
      revert s; contrapose; push_neg
      rintro ⟨np1, h⟩
      unfold Saturated; push_neg; intro coreq
      rw [coreq c1 e, coreq c2 e] at *
      use e; unfold Detects; unfold Detects'
      use c1, c2, lab
      use p2
      intro c' h1
      cases h1 with
      | inl h1=>
        rw [h1]
        unfold Cor at np1
        have r : Relevant c1 e
        · rw [←rel_relevant]; apply Relev.meas_m c2 lab
        exact cstate_regular_of_not_corrupt r np1
      | inr h1 =>
        specialize h c'
        rw [coreq c' e] at h
        replace h := h h1
        have r : Relevant c' e
        · rw [←rel_relevant]; apply Relev.meas_d c1 c2 ⟨lab, h1⟩
        replace r := cstate_some_of_relevant r
        cases r; assumption; unfold Cor at h; contradiction
    -- Formula 2
    /- I discovered a bug in the paper! Formula 2 in the paper
      holds only if φ applies only to measurement events.
      So this new Formula 2 adds the possibility that the
      event could be a corruption event. The Chase theory is
      unaffected because we never add φ facts for corruption
      events. -/
    · intro e c p; revert s; contrapose
      intro h; push_neg at h; obtain ⟨h1, h2⟩ := h
      unfold Saturated; push_neg; intro coreq; exfalso
      rw [coreq c e] at p; unfold Cor at p
      have r : Relevant c e := relevant_of_cstate _ p
      have ane := ard_nonempty_of_corrupt p
      cases ane with
      | inr ane => contradiction
      | inl ane =>
        have mc := max_adv_cor_of_corrupt h1 r ane p
        specialize h2 (max_adv r ane) (lt_of_max_adv _ ane)
        contradiction
    -- Formula 3
    -- The same bug exists for Formula 3!
    · intro e1 e2 c lt p2 lab; revert s; contrapose
      intro h; push_neg at h; obtain ⟨h1, h2⟩ := h
      unfold Saturated; push_neg; intro coreq; exfalso
      rw [coreq c e2] at p2; unfold Cor at p2
      have r : Relevant c e2 := relevant_of_cstate _ p2
      have e1ard : e1 ∈ ard c e2 := rep_in_ard lt lab
      have ane : ard c e2 ≠ ∅ := Finset.ne_empty_of_mem e1ard
      have mac := max_adv_cor_of_corrupt h1 r ane p2
      have mma := max_of_max_adv r ane
      have mlt := lt_of_max_adv r ane
      specialize mma e1 e1ard
      rw [le_iff_lt_or_eq] at mma
      cases mma with
      | inr mma => subst mma; rw [mac] at lab; cases lab
      | inl mma => specialize h2 (max_adv r ane) mma mlt; contradiction
    -- Formula 4
    · intro e1 e2 c lt lab1 lab2 r2
      revert s; contrapose; intro h; push_neg at h
      obtain ⟨h1, h2⟩ := h
      have card := cor_in_ard lt lab1
      have ane := Finset.ne_empty_of_mem card
      have mar : q.1.l (max_adv r2 ane) = cor c
      · by_cases eq : (max_adv r2 ane) = e1
        · rwa [←eq] at lab1
        · specialize h2 (max_adv r2 ane)
          have le := max_of_max_adv r2 ane e1 card
          rw [le_iff_lt_or_eq] at le;
          cases le with
          | inr le => rwa [le] at lab1
          | inl le =>
            specialize h2 le (lt_of_max_adv r2 ane)
            have al := cor_or_rep_c_of_max_adv r2 ane
            tauto
      have st := corrupt_of_max_adv_cor r2 ane mar
      cases st with
      | inr st =>
        unfold Saturated; push_neg; intro coreq; exfalso
        rw [←Cor_def, ←coreq c e2] at st
        contradiction
      | inl st =>
        simp at lab2
        rw [ms_lab_ms_lab'] at lab2; simp at lab2
        rcases lab2 with ⟨c1, c2, lab3⟩
        rw [st] at lab3; cases lab3

  · contrapose; intro s; unfold Saturated at s
    push_neg at s
    intro h
    rcases h with ⟨h1, h2, h3, h4⟩
    by_cases eq : ∀ (c : Component) (e : q.fst.Evt),
                  q.snd c e ↔ Cor q.fst c e
    · have det := s eq
      obtain ⟨e, det⟩ := det
      unfold Detects at det
      rcases det with ⟨c1, c2, det⟩
      unfold Detects' at det
      rcases det with ⟨d1, d2, d3⟩
      specialize h1 e c1 c2 d1
      rw [←Cor_def, ←eq c2 e] at d2
      specialize h1 d2
      cases h1 with
      | inl h1 =>
        specialize d3 c1; simp at d3
        rw [eq c1 e, Cor_def, d3] at h1
        cases h1
      | inr h1 =>
        rcases h1 with ⟨c3, h1, h11⟩
        specialize d3 c3; specialize d3 (Or.inr h1)
        rw [eq c3 e, Cor_def, d3] at h11
        cases h11
    · push_neg at eq
      rcases eq with ⟨c, e, niff⟩
      by_cases cor : ¬Cor q.1 c e
      · have p : q.2 c e
        · tauto
        specialize R c e
        rcases R with ⟨pcor, prep, prel⟩
        rw [Cor_def] at cor
        have csr := cstate_regular_of_not_corrupt (prel p) cor
        have rmeas := rep_or_msp_of_regular csr
        cases rmeas with
        | inl rmeas => exact prep rmeas p
        | inr rmeas =>
          have nrep : q.1.l e ≠ rep c
          · rcases rmeas with ⟨c1, c2, mlab⟩; rw [mlab]
            intro x; cases x
          have em := ard_empty_or_max_adv_rep_of_regular nrep (prel p) csr
          cases em with
          | inl em =>
            specialize h2 e c p
            cases h2 with
            | inl h2 =>
              rcases rmeas with ⟨c1, c2, rmeas⟩
              rw [rmeas] at h2; cases h2
            | inr h2 =>
              rcases h2 with ⟨e2, lt2, lab2⟩
              exact ard_ne_empty_of_cor_lt lt2 lab2 em
          | inr em =>
            obtain ⟨nem, rlab⟩ := em
            have r := prel p
            specialize h3 (max_adv r nem) e c (lt_of_max_adv r nem) p rlab
            cases h3 with
            | inl h3 =>
              rcases rmeas with ⟨c1, c2, rmeas⟩
              rw [rmeas] at h3; cases h3
            | inr h3 =>
              rcases h3 with ⟨e3, lt1, lt2, h3⟩
              have e3ard := cor_in_ard lt2 h3
              have le := max_of_max_adv r nem e3 e3ard
              replace lt1 := lt_iff_le_not_le.1 lt1
              exact lt1.2 le
      · simp at cor
        have np : ¬q.2 c e
        · tauto
        rw [Cor_def] at cor
        have cmeas := cor_or_msp_of_corrupt cor
        cases cmeas with
        | inl cmeas => exact np ((R c e).1 cmeas)
        | inr cmeas =>
          have ane := ard_nonempty_of_corrupt cor
          have lnec : q.1.l e ≠ Label.cor c
          · by_contra h; rcases cmeas with ⟨c1, c2, cmeas⟩
            rw [h] at cmeas; cases cmeas
          cases ane with
          | inr ane => contradiction
          | inl ane =>
            have r := relevant_of_cstate _ cor
            have mac := max_adv_cor_of_corrupt lnec r ane cor
            have mlt := lt_of_max_adv r ane
            have cmeas' : MeasEvt e
            · unfold MeasEvt; rw [ms_lab_ms_lab']; exact cmeas
            specialize h4 (max_adv r ane) e c mlt mac cmeas' r
            cases h4 with
            | inl h4 => contradiction
            | inr h4 =>
              rcases h4 with ⟨e', lt1, lt2, h4⟩
              have emem := rep_in_ard lt2 h4
              have maxm := max_of_max_adv r ane e' emem
              rw [lt_iff_le_not_le] at lt1
              exact lt1.2 maxm
