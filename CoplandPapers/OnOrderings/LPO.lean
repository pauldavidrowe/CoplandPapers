/-
Copyright (c) 2024 Paul D. Rowe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul D. Rowe
-/
import CoplandPapers.Confining.Labels
import CoplandPapers.Lib.lib

open scoped Classical
open Function

/-
  In this file we define the type of finite labeled partial
  orders (LPO). We define LPO homomorphisms to be Injective,
  label preserving monotone functions, and show that this
  induces a Preorder on the type LPO. We also introduce a
  structure representing the type of isomorphisms between
  lpos. These are the precisely the label-preserving
  order isomorphisms.

  We then introduce two operators (merge and earlier) that
  build new lpos out of existing ones. Merge acts as the
  disjoint union of two lpos, and earlier acts as the
  lexicographical sum of two lpos. We prove a few basic
  facts about these operators, including that they are both
  associative (up to isomorphism) and merge is commutative
  (also up to isomorphism).
-/

-- The type of finite, labeled partial orders
structure LPO (label : Type) :=
(t : Type)
(fin : Fintype t)
(po : PartialOrder t)
(l : t → label)

variable {lab : Type}

-- The underlying type for a singleton LPO.
inductive Node
| mk : Node

-- Tell Lean that Node is a Fintype.
instance Node.Fintype : Fintype Node := by
  fconstructor
  exact { Node.mk }
  intro x; cases x; simp

-- Defines a singleton LPO from a label.
def action (s : lab) : LPO lab :=
{ t := Node
  fin := Node.Fintype
  po :=
  { le := (· = ·)
    le_refl := by simp
    le_trans := by intros; simp at *
    le_antisymm := by
      intros a _ _ _
      simp [(· ≤ ·)] at * }
  l := λ _ => s
}

-- Extracts the label from the singleton LPO
@[simp]
lemma action_label {s : lab} (p : (action s).t) : (action s).l p = s := by rfl

namespace LPO

variable {l1 l2 l3 l4 : LPO lab}

-- Tells Lean that LPO are partial orders and have finite carrier type.
instance PartialOrder (l : LPO lab) : PartialOrder l.t := l.po
instance Fintype (l : LPO lab) : Fintype l.t := l.fin

/-
  Homomorphisms between lpos. These will be used
  to define a Preorder ≤ on lpos. We assume they are
  Injective to ensure that when homomorphisms
  exist in both directions, they are isomorphic.
  This will help us take the quotient and transport
  the Preorder on lpos to the quotient.
-/
@[simp]
def hom (f : l1.t → l2.t) :=
(∀ {p1 p2 : l1.t}, p1 ≤ p2 → f p1 ≤ f p2) ∧
(∀ p : l1.t, l1.l p = l2.l (f p)) ∧
(Injective f)

-- Helpful for rewriting.
lemma hom_def {f : l1.t → l2.t}:
LPO.hom f ↔
(∀ p1 p2 : l1.t, p1 ≤ p2 → f p1 ≤ f p2) ∧
(∀ p : l1.t, l1.l p = l2.l (f p)) ∧
(Injective f) := by rfl

-- Defining ≤ for the type of LPO
def le (l1 l2 : LPO lab) := ∃ f : l1.t → l2.t, LPO.hom f

instance LE : LE (LPO lab) := ⟨LPO.le⟩

-- The identity map is a homomorphism.
lemma id_hom {l : LPO lab}: LPO.hom (id : l.t → l.t) := by
  simp only [hom, id_eq, imp_self, implies_true, true_and]
  exact injective_id

lemma le_refl (a : LPO lab) : a ≤ a := ⟨id, id_hom⟩

-- Homomorphisms are transitive.
lemma le_trans (a b c : LPO lab) (ab : a ≤ b) (bc : b ≤ c) : a ≤ c := by
  obtain ⟨f1, hf1⟩ := ab
  obtain ⟨f2, hf2⟩ := bc
  use f2 ∘ f1; constructor
  · intro p1 p2 le; simp
    exact hf2.1 (hf1.1 le)
  constructor
  · intro p; simp
    have eq1 := hf1.2.1 p
    have eq2 := hf2.2.1 (f1 p); rw [eq1, eq2]
  · exact Injective.comp hf2.2.2 hf1.2.2

-- LPO forms a Preorder under ≤
instance Preorder : Preorder (LPO lab) :=
{ le := LPO.le
  le_refl := le_refl
  le_trans := le_trans
}

-- The structure of an isomorphism between two lpos.
structure iso (l1 l2 : LPO lab) :=
(order : OrderIso l1.t l2.t)
(label : ∀ p, l1.l p = l2.l (order.toFun p))

infix:25 " ≃ₑ " => iso

-- Enables the use of ≈ to assert the existence of an equivalence.
instance : HasEquiv (LPO lab) :=
{ Equiv := λ l1 l2 => ∃ _ : l1 ≃ₑ l2, true }

-- If l1 ≤ l2, and l2 ≤ l1, then l1 ≈ l2.
lemma bijective_of_hom_hom {l1 l2 : LPO lab}
{f : l1.t → l2.t} {g : l2.t → l1.t}
(hf : LPO.hom f) (hg : LPO.hom g) : Bijective f := by
  have h1 := card_eq_of_injective hf.2.2 hg.2.2
  have h2 := (Fintype.bijective_iff_injective_and_card f).2
  exact h2 ⟨hf.2.2, h1⟩

-- The homomorphisms repsect the strict order as well.
lemma lt_mono_of_mono_and_injective {α β : LPO lab}
{f : α.t → β.t}
{e1 e2 : α.t}
(hf : e1 ≤ e2 → f e1 ≤ f e2)
(inj : Injective f):
e1 < e2 → f e1 < f e2 := by
  intro lt
  have le := le_of_lt lt
  replace le := hf le
  rw [le_iff_lt_or_eq] at le
  cases le with
  | inl le => exact le
  | inr le =>
    replace le := inj le; subst le
    exfalso; exact lt_irrefl e1 lt

/-
  We introduce some facts about cardinality to help help
  show that two lpos are isomorphic when there are homomorphisms
  in both directions.
-/
lemma card_le_of_lpo_le {l1 l2 : LPO lab}
{f1 : l1.t → l2.t} (hf1 : hom f1) :
Fintype.card { p : l1.t × l1.t | p.1 < p.2 } ≤
  Fintype.card { p : l2.t × l2.t | p.1 < p.2 } := by
  have f_inj := hf1.2.2
  let F := λ p : l1.t × l1.t => (f1 p.1, f1 p.2)
  have : ∀ p : l1.t × l1.t,
    p ∈ { p : l1.t × l1.t | p.1 < p.2 } →
    F p ∈ { p : l2.t × l2.t | p.1 < p.2 }
  · simp; intros e1 e2 mem
    apply lt_mono_of_mono_and_injective hf1.1 hf1.2.2 mem
  set F' : { p : l1.t × l1.t | p.1 < p.2 } →
           { p : l2.t × l2.t | p.1 < p.2 } :=
        λ p => ⟨F p, this p p.2⟩ with Fdef'
  have hF' : Injective F'
  · intro p1 p2 eq; rw [Fdef'] at eq; simp at eq
    ext
    · apply f_inj; aesop
    · apply f_inj; aesop
  apply Fintype.card_le_of_injective F' hF'

lemma card_eq_of_lpo_le_le {l1 l2 : LPO lab}
{f1 : l1.t → l2.t} (hf1 : LPO.hom f1)
{f2 : l2.t → l1.t} (hf2 : LPO.hom f2) :
Fintype.card { p : l1.t × l1.t | p.1 < p.2 } =
Fintype.card { p : l2.t × l2.t | p.1 < p.2 } := by
  rw [eq_iff_le_not_lt]; constructor
  · use card_le_of_lpo_le hf1
  · apply not_lt_of_le
    exact card_le_of_lpo_le hf2

lemma card_lt_of_rel_not_surj' {l1 l2 : LPO lab}
{f1 : l1.t → l2.t} (hf1 : hom f1)
(hc : ∃ e1 e2, f1 e1 < f1 e2 ∧ ¬e1 < e2) :
Fintype.card { p : l1.t × l1.t | p.1 < p.2 } <
Fintype.card { p : l2.t × l2.t | p.1 < p.2 } := by
  have f_inj := hf1.2.2
  let F' := λ p : l1.t × l1.t => (f1 p.1, f1 p.2)
  have h1 : ∀ p, p ∈ { p : l1.t × l1.t | p.1 < p.2 } →
            (F' p) ∈ { p : l2.t × l2.t | p.1 < p.2 }
  · intro p mem; simp at mem
    simp only [Set.mem_setOf_eq]
    exact lt_mono_of_mono_and_injective hf1.1 hf1.2.2 mem
  rcases hc with ⟨e1, e2, lt2, nlt1⟩
  set F : { p : l1.t × l1.t | p.1 < p.2 } →
          { p : l2.t × l2.t | p.1 < p.2 } :=
    λ p => ⟨F' p, h1 p p.2⟩ with Fdef'
  have F_inj : Injective F
  · intro p1 p2 eq; rw [Fdef'] at eq; simp at eq
    ext
    apply f_inj; aesop
    apply f_inj; aesop
  have F_nsurj : ¬Surjective F
  · intro F_surj
    specialize F_surj ⟨(f1 e1, f1 e2), lt2⟩
    cases' F_surj with a Feq
    rw [Fdef'] at Feq; simp [F'] at Feq
    cases' Feq with Feq1 Feq2
    replace Feq1 := hf1.2.2 Feq1
    replace Feq2 := hf1.2.2 Feq2
    have a2 := a.2; simp at a2
    rw [Feq1, Feq2] at a2; contradiction
  apply Fintype.card_lt_of_injective_not_surjective F F_inj F_nsurj

-- Small API for equivalence of lpos.
lemma equiv_def' :
l1 ≈ l2 ↔ l1 ≤ l2 ∧ l2 ≤ l1 := by
  constructor
  · intro eqv
    rcases eqv with ⟨⟨e, he⟩, tmp⟩; clear tmp
    constructor
    · use e.toFun
      constructor
      · simp
      · use he
        apply LeftInverse.injective e.toEquiv.left_inv
    · use e.invFun
      constructor
      · simp
      · constructor
        · intro p2
          specialize he (e.invFun p2)
          simp only [Equiv.invFun_as_coe, OrderIso.toEquiv_symm, RelIso.coe_fn_toEquiv,
            Equiv.toFun_as_coe, OrderIso.apply_symm_apply] at he
          rw [←he]; simp
        · apply RightInverse.injective e.toEquiv.right_inv
  · rintro ⟨le1, le2⟩
    cases' le1 with f1 hf1
    cases' le2 with f2 hf2
    by_cases ne : (Nonempty l1.t); swap
    · simp at ne
      have : IsEmpty l2.t
      · apply Function.isEmpty f2
      exact ⟨{
        order := {
          toFun := λ x => by
            exfalso; rw [isEmpty_iff] at ne
            exact ne x
          invFun := λ x => by
            exfalso; rw [isEmpty_iff] at this
            exact this x
          left_inv := by
            intro x; exfalso
            rw [isEmpty_iff] at ne; exact ne x
          right_inv := by
            intro x; exfalso
            rw [isEmpty_iff] at this; exact this x
          map_rel_iff' := by
            intro x; exfalso
            rw [isEmpty_iff] at ne; exact ne x
          },
        label := by
          intro x; exfalso; rw [isEmpty_iff] at ne; exact ne x
      }, by triv⟩
    · have bij := bijective_of_hom_hom hf1 hf2
      constructor; triv
      exact {
        order :=
        {
          toFun := f1
          invFun := invFun f1
          left_inv := leftInverse_invFun bij.1
          right_inv := rightInverse_invFun bij.2
          map_rel_iff' := by
            simp only [Equiv.coe_fn_mk]
            intro a b
            constructor
            · intro le
              by_contra h
              apply card_eq_of_lpo_le_le hf1 at hf2
              --have H1 := card_eq_of_lpo_le_le hf1
              have H2 := card_lt_of_rel_not_surj' hf1
              have H3 : ∃ (e1 e2 : l1.t), f1 e1 < f1 e2 ∧ ¬e1 < e2
              · use a, b
                --use [(inv_fun f1) (f1 e1), (inv_fun f1) (f1 e2)],
                constructor; swap
                · rw [le_iff_lt_or_eq] at h; push_neg at h
                  exact h.1
                · rw [le_iff_lt_or_eq] at le
                  cases le with
                  | inl le => exact le
                  | inr le =>
                    replace le := hf1.2.2 le; subst le
                    exfalso; apply h; rfl
              specialize H2 H3
              rw [eq_iff_le_not_lt] at hf2
              exact hf2.2 H2
            · intro le; exact hf1.1 le
        }
        label := hf1.2.1 }

lemma equiv_def :
l1 ≈ l2 ↔ ∃ _ : l1 ≃ₑ l2, true := by rfl

-- Parallel composition of two lpos
def merge (l1 l2 : LPO lab) : LPO lab :=
{ t := l1.t ⊕ l2.t,
  fin := instFintypeSum l1.t l2.t
  po := Sum.instPartialOrderSum
  l := λ e => by
    cases e with
    | inl e => exact l1.l e
    | inr e => exact l2.l e
}

namespace merge
-- Basic facts about merge

-- Simp lemmas to extract the labels from a merge
@[simp]
lemma label_inl {p1 : l1.t} :
  (merge l1 l2).l (.inl p1) = l1.l p1 := rfl

@[simp]
lemma label_inr {p2 : l2.t} :
 (merge l1 l2).l (.inr p2) = l2.l p2 := rfl

-- Both s and t have homs into merge s t
lemma le_left : l1 ≤ merge l1 l2 := by
  fconstructor; intro p; use .inl p
  constructor
  · exact fun {p1 p2} a => Sum.LiftRel.inl a
  constructor
  · simp
  · exact Sum.inl_injective

lemma le_right : l2 ≤ merge l1 l2 := by
  fconstructor; intro p; use .inr p
  constructor
  · exact fun {p1 p2} a => Sum.LiftRel.inr a
  constructor
  · simp
  · exact Sum.inr_injective

-- Merge is associative
def assoc (l1 l2 l3 : LPO lab) :
merge (merge l1 l2) l3 ≃ₑ merge l1 (merge l2 l3) :=
{ order := OrderIso.sumAssoc l1.t l2.t l3.t
  label := by
    intro e;
    cases e with
    | inl e => cases e with
      | inl e => rfl
      | inr e => rfl
    | inr e => rfl
}

-- This is used in qlpo
def assoc' (l1 l2 l3 : LPO lab) :
merge (merge l1 l2) l3 ≈ merge l1 (merge l2 l3) := by
constructor; triv
exact
{ order := OrderIso.sumAssoc l1.t l2.t l3.t
  label := by
    intro e;
    cases e with
    | inl e => cases e with
      | inl e => rfl
      | inr e => rfl
    | inr e => rfl
}

-- Merge is commutative
def comm (l1 l2 : LPO lab):
merge l1 l2 ≃ₑ merge l2 l1 :=
{ order := OrderIso.sumComm l1.t l2.t,
  label := by intro e; cases e; rfl; rfl
}

-- This is used in qlpo
def comm' (l1 l2 : LPO lab):
merge l1 l2 ≈ merge l2 l1 := by
constructor; triv
exact {
  order := OrderIso.sumComm l1.t l2.t
  label := by intro e; cases e; rfl; rfl
}

lemma merge_inl_le_inr (a : l1.t) (b : l2.t) :
toLex (Sum.inl a : (merge l1 l2).t) ≤ toLex (Sum.inr b) := by
  simp

-- The image of a in merge s t is either in s or it's in t
lemma inl_or_inr_of_lpo_hom
{f : l1.t → (merge l2 l3).t} --(hf : LPO.hom f)
(a : l1.t) :
(∃ b : l2.t, f a = .inl b) ∨ (∃ c : l3.t, f a = .inr c) := by
  cases' (f a) with b c
  left; use b; right; use c

-- Given two functions from gs and gt into s and t respectively,
-- create a function from the merge of gs and gt into the merge of s and t.
def merge_le_merge_fun {gs gt s t : LPO lab} (fs : gs.t → s.t)
(ft : gt.t → t.t) : (merge gs gt).t → (merge s t).t :=
λ st =>
  match st with
  | .inl ps => (.inl (fs ps))
  | .inr pt => (.inr (ft pt))

-- The function defined above is an LPO hom.
lemma merge_merge_le (le1 : l1 ≤ l3) (le2 : l2 ≤ l4) :
merge l1 l2 ≤ merge l3 l4 := by
  cases' le1 with f1 hf1; cases' le2 with f2 hf2
  use LPO.merge.merge_le_merge_fun f1 f2
  constructor
  · intro p1 p2 le
    cases p1 <;> cases p2
    · simp [LPO.merge.merge_le_merge_fun]
      rw [Sum.inl_le_inl_iff] at le
      exact Sum.LiftRel.inl (hf1.1 le)
    · cases le
    · cases le
    · simp [LPO.merge.merge_le_merge_fun]
      rw [Sum.inr_le_inr_iff] at le
      exact Sum.LiftRel.inr (hf2.1 le)
  constructor
  · intro p; rcases p with p | p
    · simp [LPO.merge.merge_le_merge_fun]
      exact hf1.2.1 p
    · simp [LPO.merge.merge_le_merge_fun]
      exact hf2.2.1 p
  · intro p1 p2 eq
    cases p1 <;> cases p2
    · simp [LPO.merge.merge_le_merge_fun] at eq
      rw [Sum.inl.inj_iff] at eq ⊢
      exact hf1.2.2 eq
    · cases eq
    · cases eq
    · simp [LPO.merge.merge_le_merge_fun] at eq
      rw [Sum.inr.inj_iff] at eq ⊢
      exact hf2.2.2 eq

-- A singleton that is ≤ merge s t is ≤ s or is ≤ t
lemma action_le_merge {l : lab}
(le : action l ≤ l1.merge l2) : action l ≤ l1 ∨ action l ≤ l2 := by
  obtain ⟨f, hf⟩ := le
  --set a := (f Node.mk) with ha
  cases eq : (f Node.mk) with
  | inl y =>
    left; use λ _ => y
    constructor
    · simp
    constructor
    · intro p
      have h1 := hf.2.1 Node.mk
      simp at h1 ⊢
      rw [h1, eq]
      rfl
    · intro p1 p2 eq; cases p1; cases p2; rfl
  | inr y =>
    right; use λ _ => y
    constructor
    · simp
    constructor
    · intro p
      have h1 := hf.2.1 Node.mk
      simp at h1 ⊢
      rw [h1, eq]
      rfl
    · intro p1 p2 eq; cases p1; cases p2; rfl

-- We can extend a hom into a merge of the target on either left or right
lemma le_merge_of_le_left
(le : l1 ≤ l2) : l1 ≤ l2.merge l3 := by
  cases' le with f hf
  use λ x => (.inl (f x))
  constructor
  · intro p1 p2 le
    simp;
    exact Sum.LiftRel.inl (hf.1 le)
  constructor
  · exact hf.2.1
  · intro p1 p2 eq; simp at eq
    rw [Sum.inl.injEq] at eq
    exact hf.2.2 eq

lemma le_merge_of_le_right (le : l1 ≤ l3) : l1 ≤ l2.merge l3 := by
  cases' le with f hf
  use λ x => (.inr (f x))
  constructor
  · intro p1 p2 le
    simp; exact Sum.LiftRel.inr (hf.1 le)
  constructor
  · exact hf.2.1
  · intro p1 p2 eq; simp at eq
    rw [Sum.inr.injEq] at eq
    exact hf.2.2 eq

end merge

-- Sequential composition of two lpos
def earlier (l1 l2 : LPO lab) : LPO lab :=
{ t := l1.t ⊕ₗ l2.t
  fin := Lex.fintype (l1.t ⊕ l2.t)
  po := Sum.Lex.partialOrder
  l := λ e => by
    rcases e with e | e; exact l1.l e; exact l2.l e
}

namespace Earlier
-- Basic facts about earlier, almost entirely analagous to merge

-- Something about type synonym for earlier doesn't unify well,
-- so we need results for the explicit toLex version and for
-- the simpler notation.
@[simp]
lemma label_inl {p : l1.t} :
  (earlier l1 l2).l (.inl p) = l1.l p := rfl

@[simp]
lemma label_inl' {p : l1.t} :
  (earlier l1 l2).l (.inl p) = l1.l p := rfl

@[simp]
lemma label_inr {p : l2.t}:
  (earlier l1 l2).l (.inr p) = l2.l p := rfl

@[simp]
lemma label_inr' {p : l2.t} :
  (earlier l1 l2).l (.inr p) = l2.l p := rfl

lemma le_left : l1 ≤ earlier l1 l2 := by
  fconstructor; intro p; use (.inl p)
  constructor
  · exact fun {p1 p2} a => Sum.Lex.inl a
  constructor
  · intro p; simp
  · exact Sum.inl_injective

lemma le_right : l2 ≤ earlier l1 l2 := by
  fconstructor; intro p; use (.inr p)
  constructor
  · exact fun {p1 p2} a => Sum.Lex.inr a
  constructor
  · intro p; simp
  · exact Sum.inr_injective

-- This is needed because the cases tactic on
-- toLex sum doesn't work right.
/- lemma cases (p : (earlier l1 l2).t) :
(∃ p1 : l1.t, p = (.inl p1)) ∨
(∃ p2 : l2.t, p = (.inr p2)) := by
  cases p with
  | inl p => left; use p;
  | inr p => right; use p; -/

def assoc (l1 l2 l3 : LPO lab) :
earlier (earlier l1 l2) l3 ≃ₑ earlier l1 (earlier l2 l3) :=
{ order := OrderIso.sumLexAssoc l1.t l2.t l3.t,
  label := by
    intro p
    cases p with
    | inl p => cases p with
      | inl p => rfl
      | inr p => rfl
    | inr p => rfl
}

-- This is used in qlpo
def assoc' (l1 l2 l3 : LPO lab) :
earlier (earlier l1 l2) l3 ≈ earlier l1 (earlier l2 l3) :=
by
  constructor; triv
  exact {
  order := OrderIso.sumLexAssoc l1.t l2.t l3.t
  label := by
    intro p
    cases p with
    | inl p => cases p with
      | inl p => rfl
      | inr p => rfl
    | inr p => rfl
  }

def earlier_le_earlier_fun {gs gt s t : LPO lab} (fs : gs.t → s.t) (ft : gt.t → t.t) :
(earlier gs gt).t → (earlier s t).t :=
λ st =>
  match st with
  | .inl ps => .inl (fs ps)
  | .inr pt => .inr (ft pt)

lemma earlier_earlier_le (le1 : l1 ≤ l3) (le2 : l2 ≤ l4) :
earlier l1 l2 ≤ earlier l3 l4 := by
  obtain ⟨f1, hf1⟩ := le1
  obtain ⟨f2, hf2⟩ := le2
  use LPO.Earlier.earlier_le_earlier_fun f1 f2
  constructor
  · intro p1 p2 le
    --have p1 := LPO.earlier.cases p11
    --have p2 := LPO.earlier.cases p22
    cases p1 with
    | inl p1 => cases p2 with
      | inl p2 =>
        apply Sum.Lex.inl_le_inl_iff.mp at le
        simp [LPO.Earlier.earlier_le_earlier_fun]
        apply Sum.Lex.inl;
        exact hf1.1 le
      | inr p2 =>
        simp [LPO.Earlier.earlier_le_earlier_fun]
        exact Sum.Lex.sep (f1 p1) (f2 p2)
    | inr p1 => cases p2 with
      | inl p2 => cases le
      | inr p2 =>
        apply Sum.Lex.inr_le_inr_iff.mp at le
        simp [LPO.Earlier.earlier_le_earlier_fun]
        apply Sum.Lex.inr
        exact hf2.1 le
  constructor
  · intro p1
    cases p1 with
    | inl p1 =>
      simp [LPO.Earlier.earlier_le_earlier_fun]
      rw [hf1.2.1 p1]
    | inr p1 =>
      simp [LPO.Earlier.earlier_le_earlier_fun]
      rw [hf2.2.1 p1]
  · intro p1 p2 eq
    cases p1 with
    | inl p1 => cases p2 with
      | inl p2 =>
        simp [LPO.Earlier.earlier_le_earlier_fun] at eq
        rw [Sum.inl.inj_iff] at eq ⊢
        exact hf1.2.2 eq
      | inr p2 =>
        cases eq
    | inr p1 => cases p2 with
      | inl p2 => cases eq
      | inr p2 =>
        simp [LPO.Earlier.earlier_le_earlier_fun] at eq
        rw [Sum.inr.inj_iff] at eq ⊢
        exact hf2.2.2 eq


end Earlier
end LPO
