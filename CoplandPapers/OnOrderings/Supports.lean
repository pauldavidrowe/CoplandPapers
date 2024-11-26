/-
Copyright (c) 2024 Paul D. Rowe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul D. Rowe
-/
import CoplandPapers.OnOrderings.CoplandOrder
import CoplandPapers.OnOrderings.AttackTrees

namespace Supports
open AttackTree Copland
variable {lab : Type} {p : Place}

/-
  Type synonym for attack trees ordered by the Supports preorder
  Without the type synonyms, the instances for the covers order
  and the Supports order will conflict.

  This was originally to avoid confining the order instances to
  sections, but sections turn out to be necessary after all.
  The rest of this might be simplified or easier to read without
  these type synonyms. But we're stuck with them for now.

  These orders are "contravariant" in the sense that t1 ≤ t2
  means we are looking for homomorphisms from the semantics of t2
  to the semantics of t1.
-/
abbrev AttSup (lab : Type) := AttackTree lab

-- Tell Lean AttSup forms a preorder
local instance : Preorder (AttSup lab) := AT.supports_preorder lab

-- Type synonym for Copland phrases at a given Place p,
-- ordered by Supports
abbrev CopSup (_ : Place) := Copland

-- Tell Lean CopSup p forms a preorder
local instance : Preorder (CopSup p) := Copland.supports_preorder p

-- Coercing atoms into the type synonym. It's just a way of
-- providing p since the type synonym requires it.
@[simp]
def sup.atom (p : Place) (a : ASP) : CopSup p := Copland.atom a

-- Coercing bpar into the type synonym
@[simp]
def sup.bpar {p : Place} (s : Split) (c1 c2 : CopSup p) : CopSup p := Copland.bpar s c1 c2

section
-- See Covers.lean for explanation
--local attribute [reducible] AttSup CopSup

-- API for ≤ for attack trees
lemma AT.le_def {t1 t2 : AttSup lab} :
t1 ≤ t2 ↔
∀ H, H ∈ BS t1 → ∃ G, G ∈ BS t2 ∧ G ≤ H := by rfl

-- API for ≤ for Copland phrases
lemma Cop.le_def {c1 c2 : CopSup p} :
c1 ≤ c2 ↔
∀ H, H ∈ copland_base_sem p c1 → ∃ G, G ∈ copland_base_sem p c2 ∧ G ≤ H := by rfl

-- Attack tree atoms ordered by ≤ must be equal
lemma atm_le_atm {t1 t2 : lab} :
  (atm t1) ≤ (atm t2) → t1 = t2 := by
  intro le; rw [AT.le_def] at le
  specialize le (qaction t1) (by simp [BS])
  rcases le with ⟨t2a, t2amem, le⟩
  simp [BS] at t2amem; subst t2amem
  change qaction t2 ≤ qaction t1 at le
  exact (eq_of_qaction_le le).symm

-- Copland atoms ordered by ≤ must be equal
lemma atom_le_atom {a1 a2 : ASP} :
  sup.atom p a1 ≤ atom a2 → a1 = a2 := by
  intro le
  specialize le (qaction (asp_label a1)) (by simp)
  rcases le with ⟨c2a, c2amem, le⟩
  simp at c2amem; subst c2amem; symm
  change qaction (asp_label a2) ≤ qaction (asp_label a1) at le
  have := @eq_of_qaction_le _ (asp_label a2) (asp_label a1) le
  cases a1 <;> cases a2 <;> cases this <;> rfl

-- An atom ≤ t1 ∨ t2 must be ≤ t1 or ≤ t2
lemma atm_le_or {t1 : lab} {t21 t22 : AttackTree lab} :
(atm t1) ≤ (t21.or t22) ↔ (atm t1) ≤ t21 ∨ (atm t1) ≤ t22 := by
  constructor <;> intro le
  · rw [AT.le_def] at le ⊢
    specialize le (qaction t1) (by simp [BS])
    rcases le with ⟨t2, t2mem, le⟩
    cases t2mem with
    | inl t2mem =>
      left
      intro H Hmem; simp at Hmem; subst Hmem;
      use t2, t2mem; exact le
    | inr t2mem =>
      right
      intro H Hmem; simp at Hmem; subst Hmem
      use t2, t2mem; exact le
  · cases le with
    | inl le =>
      specialize le (qaction t1) (by simp)
      rcases le with ⟨t, tmem, le⟩
      intro H Hmem; simp at Hmem; subst Hmem
      have l := Quotient.exists_rep t
      obtain ⟨l, eq⟩ := l; rw [←eq] at tmem
      have inh := BS_inhabited tmem
      have eq1 := QLPO.merge.any_le_qaction eq.symm inh le
      use t; rw [eq] at tmem
      constructor
      · simp; left; exact tmem
      · exact le
    | inr le =>
      specialize le (qaction t1) (by simp)
      rcases le with ⟨t, tmem, le⟩
      intro H Hmem; simp at Hmem; subst Hmem
      have l := Quotient.exists_rep t
      obtain ⟨l, eq⟩ := l; rw [←eq] at tmem
      have inh := BS_inhabited tmem
      have eq1 := QLPO.merge.any_le_qaction eq.symm inh le
      use t; rw [eq] at tmem
      constructor
      · simp; right; exact tmem
      · exact le

-- An atom cannot be ≤ a conjuctive attack tree
lemma atm_le_and {t1 : lab} {t21 t22 : AttackTree lab}
(le : (atm t1) ≤ t21.and t22) : false := by
  rw [AT.le_def] at le
  specialize le (qaction t1) (by simp [BS])
  rcases le with ⟨t2, t2mem, le⟩
  simp [BS, (· ⋈ ·)] at t2mem
  rcases t2mem with ⟨t3, t3mem, ⟨t4, t4mem, eq⟩⟩
  subst eq
  obtain ⟨l3, hl3⟩ := Quotient.exists_rep t3
  obtain ⟨l4, hl4⟩ := Quotient.exists_rep t4
  rw [←hl3] at t3mem le; rw [←hl4] at t4mem le
  have l3i := BS_inhabited t3mem
  have l4i := BS_inhabited t4mem
  exact QLPO.merge.inhabited_merge_nle_singleton l3i l4i le

-- An atom cannot be ≤ a branching parallel phrase
lemma atom_le_bpar {a : ASP} {c1 c2 : CopSup p} {s : Split}
(le : sup.atom p a ≤ bpar s c1 c2) : false := by
  specialize le (qaction (asp_label a)) (by simp [copland_base_sem])
  rcases le with ⟨G, Gmem, le⟩
  simp [copland_base_sem] at Gmem
  subst Gmem; obtain ⟨f, hf⟩ := le
  have all_eq : ∀ x, (f x) = Node.mk;
  · intro x; cases (f x); rfl
  have xnode := all_eq (.inl Node.mk)
  have ynode := all_eq (.inr (.inr Node.mk))
  rw [←xnode] at ynode
  replace ynode := hf.2.2 ynode
  cases ynode

-- An atom cannot be ≤ a sequential tree
lemma atm_le_seq {t1 : lab} {t21 t22 : AttackTree lab}
(le : (atm t1) ≤ t21.seq t22) : false := by
  rw [AT.le_def] at le
  specialize le (qaction t1) (by simp [BS])
  rcases le with ⟨t2, t2mem, le⟩
  simp [BS, (· ↝ ·)] at t2mem
  rcases t2mem with ⟨t3, t3mem, ⟨t4, t4mem, eq⟩⟩
  subst eq
  obtain ⟨l3, hl3⟩ := Quotient.exists_rep t3
  obtain ⟨l4, hl4⟩ := Quotient.exists_rep t4
  rw [←hl3] at t3mem le; rw [←hl4] at t4mem le
  have l3i := BS_inhabited t3mem
  have l4i := BS_inhabited t4mem
  exact QLPO.Earlier.inhabited_earlier_nle_singleton l3i l4i le

-- An atom cannot be ≤ a branching sequential phrase
lemma atom_le_bseq {a : ASP} {c1 c2 : CopSup p} {s : Split}
(le : sup.atom p a ≤ bseq s c1 c2) : false := by
  specialize le (qaction (asp_label a)) (by simp [copland_base_sem])
  rcases le with ⟨G, Gmem, le⟩
  simp [copland_base_sem] at Gmem
  subst Gmem; obtain ⟨f, hf⟩ := le
  have all_eq : ∀ x, (f x) = Node.mk;
  · intro x; cases (f x); rfl
  have xnode := all_eq (.inl Node.mk)
  have ynode := all_eq (.inr (.inr Node.mk))
  rw [←xnode] at ynode
  replace ynode := hf.2.2 ynode
  cases ynode

-- An atom cannot be ≤ a linear sequential phrase
lemma atom_le_lseq {a : ASP} {c1 c2 : CopSup p}
(le : sup.atom p a ≤ lseq c1 c2) : false := by
  specialize le (qaction (asp_label a)) (by simp [copland_base_sem])
  rcases le with ⟨G, Gmem, le⟩
  simp [copland_base_sem] at Gmem
  subst Gmem; obtain ⟨f, hf⟩ := le
  haveI hx := cop_sem_inhabited p c1
  haveI hy := cop_sem_inhabited p c2
  have all_eq : ∀ x, (f x) = Node.mk;
  · intro x; cases (f x); rfl
  have xnode := all_eq (.inl default)
  have ynode := all_eq (.inr default)
  rw [←xnode] at ynode
  replace ynode := hf.2.2 ynode
  cases ynode

-- An atom cannot be ≤ a remote request phrase
lemma atom_le_att {a : ASP} {c1 : CopSup p} {q : Place}
(le : sup.atom p a ≤ att q c1) : false := by
  specialize le (qaction (asp_label a)) (by simp [copland_base_sem])
  rcases le with ⟨G, Gmem, le⟩
  simp [copland_base_sem] at Gmem
  subst Gmem; obtain ⟨f, hf⟩ := le
  --set x := (f (sum.inl Node.mk)) with hx,
  --set y := (f (sum.inr (sum.inr Node.mk))) with hy,
  have all_eq : ∀ x, (f x) = Node.mk;
  · intro x; cases (f x); rfl
  have xnode := all_eq (.inl Node.mk)
  have ynode := all_eq (.inr (.inr Node.mk))
  rw [←xnode] at ynode
  replace ynode := hf.2.2 ynode
  cases ynode

-- If a disjunctive tree is ≤ t, then one of its disjuncts is ≤ t
lemma or_le_any_at {t11 t12 t2 : AttackTree lab}
(le : t11.or t12 ≤ t2) : t11 ≤ t2 ∧ t12 ≤ t2 := by
  rw [AT.le_def] at le
  constructor
  all_goals
    intro H Hmem
    have Hmem' : H ∈ BS (t11.or t12); simp [BS]; tauto
    exact le H Hmem'

-- If a conjuctive tree is ≤ an atom, then one of its conjuncts is
lemma and_le_atm {t11 t12 : AttackTree lab} {t2 : lab}
(le : t11.and t12 ≤ (atm t2)) : t11 ≤ (atm t2) ∨ t12 ≤ (atm t2) := by
  rw [AT.le_def] at le
  by_contra h; push_neg at h
  obtain ⟨h1, h2⟩ := h
  rw [AT.le_def] at h1 h2; push_neg at h1 h2
  rcases h1 with ⟨H1, H1mem, h1⟩
  rcases h2 with ⟨H2, H2mem, h2⟩
  specialize h1 (qaction t2) (by simp [BS])
  specialize h2 (qaction t2) (by simp [BS])
  specialize le (H1 ⊎ H2)
  simp [BS] at le
  obtain ⟨H1', H1eq⟩ := Quotient.exists_rep H1
  obtain ⟨H2', H2eq⟩ := Quotient.exists_rep H2
  rw [←H1eq, ←H2eq] at le
  change ⟦H1'.merge H2'⟧ ∈ BS t11 ⋈ BS t12 → ⟦action t2⟧ ≤ ⟦H1'⟧ ⊎ ⟦H2'⟧ at le
  rw [QLPO.mem_dist_prod_iff] at le
  have input : ∃ (la lb : LPO lab), ⟦H1'.merge H2'⟧ = ⟦la⟧ ⊎ ⟦lb⟧ ∧ ⟦la⟧ ∈ BS t11 ∧ ⟦lb⟧ ∈ BS t12
  · use H1', H2', by rfl
    rw [←H1eq] at H1mem; rw [←H2eq] at H2mem
    exact ⟨H1mem, H2mem⟩
  specialize le input
  replace le := QLPO.merge.le_left_or_right_of_singleton le
  rw [H1eq] at le
  rw [H2eq] at le
  tauto

-- If a bpar phrase is ≤ an atom, then one of its branches is
lemma bpar_le_atom {c1 c2 : CopSup p} {a : ASP} {s : Split}
(le : (sup.bpar s c1 c2) ≤ sup.atom p a) :
c1 ≤ sup.atom p a ∨ c2 ≤ sup.atom p a := by
  rw [Cop.le_def] at le
  specialize le ⟦LPO.earlier (evsys_of_label Label.split)
     ((LPO.merge (cop_sem p c1) (cop_sem p c2)).earlier
       (evsys_of_label Label.joins))⟧ (by simp)
  rcases le with ⟨G, Gmem, le⟩
  simp at Gmem; subst Gmem
  obtain ⟨f, hf⟩ := le
  have biglab := hf.2.1 Node.mk
  cases h : (f Node.mk) with
  | inl val =>
    exfalso
    rw [h] at biglab; simp at biglab
  | inr val => cases val with
    | inl val =>
      cases val with
      | inl val =>
        left
        rw [Cop.le_def]
        intros H Hmem
        use qaction (asp_label a); simp
        simp at Hmem; subst Hmem
        use λ _ => val
        constructor
        · simp
        constructor
        · intro p1
          have peq : p1 = Node.mk; cases p1; rfl
          subst peq
          simp at biglab
          rw [h] at biglab
          rw [biglab]; simp
        · intro p1 p2 eq; cases p1; cases p2; rfl
      | inr val =>
        right
        rw [Cop.le_def]
        intro H Hmem
        use qaction (asp_label a); simp
        simp at Hmem; subst Hmem
        use λ _ => val
        constructor
        · simp
        constructor
        · intro p1
          have peq : p1 = Node.mk; cases p1; rfl
          subst peq
          rw [h] at biglab
          rw [biglab]; rfl
        · intros p1 p2 eq; cases p1; cases p2; rfl
    | inr val =>
      exfalso
      rw [h] at biglab; simp at biglab

-- A conjunctive tree is ≤ an atom if its left conjunct is
lemma le_and_left_of_le_atom {t1 t2 : AttSup lab} {l : lab}
(le : t1 ≤ atm l) : t1.and t2 ≤ atm l := by
  rw [AT.le_def] at le
  intro H Hmem; simp at Hmem
  have ha := Quotient.exists_rep H
  obtain ⟨a, ha⟩ := ha; rw [←ha] at Hmem
  rw [QLPO.mem_dist_prod_iff] at Hmem
  rcases Hmem with ⟨la, lb, eq, hla, _⟩
  specialize le ⟦la⟧ hla
  rcases le with ⟨G, Gmem, le⟩
  use G, Gmem
  rw [←ha, eq]
  exact QLPO.merge.le_merge_of_le_left le

-- A conjunctive tree is ≤ an atom if its right conjunct is
lemma le_and_right_of_le_atom {t1 t2 : AttSup lab} {l : lab}
(le : t2 ≤ atm l) : t1.and t2 ≤ atm l := by
  rw [AT.le_def] at le
  intro H Hmem; simp at Hmem
  have ha := Quotient.exists_rep H
  obtain ⟨a, ha⟩ := ha; rw [←ha] at Hmem
  rw [QLPO.mem_dist_prod_iff] at Hmem
  rcases Hmem with ⟨la, lb, eq, _, hlb⟩
  specialize le ⟦lb⟧ hlb
  rcases le with ⟨G, Gmem, le⟩
  use G, Gmem
  rw [←ha, eq]
  exact QLPO.merge.le_merge_of_le_right le

end
end Supports
