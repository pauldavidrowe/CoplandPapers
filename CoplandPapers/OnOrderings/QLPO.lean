import CoplandPapers.OnOrderings.LPO

open Function 

/- 
  This file introduces the Quotient of lpos by the equivalence
  relation induced by isomorphism. We show that this is indeed
  an equivalence relation and then form the Setoid of lpos
  under that relation. Setoids are what Lean uses to define 
  quotients. The resulting Quotient type is called QLPO. 

  By showing that (≤) on lpos plays nicely with isomorphisms,
  we then transport (≤) to a Preorder on QLPO. (We should 
  acutally be able to prove it is a partial order on QLPO.)
  We similarly transport the merge and Earlier operators from
  lpos to qlpos introducing the notation ⊎ and ▷ respectively.
  The same basic results of these operators hold in the Quotient,
  except they now hold up to equality, not just up to isomorphism. 

  Finally, we introduce the distributive produce (⋈) and the
  pointwise sequential composition (↝) operators for sets of
  qlpos. 
-/


namespace LPO
open OrderIso 

-- Arbitrary type of labels 
variable {lab : Type}

variable (l1 l2 : LPO lab)

-- Show that ≃ₑ is reflexive, symmetric, and transitive. 
def iso.refl (l1 : LPO lab) : l1 ≃ₑ l1 :=
{ order := 
 { toFun := id
   invFun := id
   left_inv := by intros x; simp
   right_inv := by intros x; simp
   map_rel_iff' := by simp }
  label := by simp
}

def iso.symm {l1 l2 : LPO lab} (I : l1 ≃ₑ l2) : l2 ≃ₑ l1 :=
{ order := I.order.symm
  label := by
   simp only [toFun_eq_coe]
   intro p; symm; have lab := I.label
   specialize lab ((I.order.symm) p) 
   simp only [toFun_eq_coe, apply_symm_apply] at *
   exact lab
}

def iso.trans {l1 l2 l3 : LPO lab} (I1 : l1 ≃ₑ l2) (I2 : l2 ≃ₑ l3) :
l1 ≃ₑ l3 :=
{ order := 
  { toFun := I2.order.toFun ∘ I1.order.toFun
    invFun := I1.order.invFun ∘ I2.order.invFun
    left_inv := by intros x; simp
    right_inv := by intros x; simp
    map_rel_iff' := by simp },
  label := by
    intro p; rw [I1.label p]
    rw [I2.label (I1.order.toEquiv.toFun p)]
    rfl
}

-- Indeed ≃ₑ forms an equivalence relation. 
-- The Setoid structure allows us to take a Quotient. 
instance Setoid : Setoid (LPO lab) :=
{ r := λ l1 l2 => ∃ _ : LPO.iso l1 l2, true,
  iseqv := by
    constructor
    · intro x; use iso.refl x
    · rintro l1 l2 ⟨I, hI⟩
      use iso.symm I
    · rintro l1 l2 le ⟨I1, _⟩ ⟨I2, h2⟩
      use iso.trans I1 I2
}

end LPO 

-- The type of lpos quotiented by ≃ₑ
def QLPO (lab : Type) := Quotient (@LPO.Setoid lab)

namespace LPO 
variable {lab : Type}

-- Could be in LPO section, but it's primarily used
-- to show well-definedness of ≤ for qlpos. 
lemma equiv_equiv_mono (a1 a2 b1 b2 : LPO lab) (eqv1 : a1 ≈ b1)
(eqv2 : a2 ≈ b2) : (a1 ≤ a2) → (b1 ≤ b2) := by
  rcases eqv1 with ⟨⟨ord1, lab1⟩, h1⟩
  rcases eqv2 with ⟨⟨ord2, lab2⟩, h2⟩ 
  clear h1 h2
  rintro ⟨f, hf⟩
  use (ord2.toFun ∘ f ∘ ord1.invFun)
  constructor
  · intro p1 p2 le
    simp only [OrderIso.toFun_eq_coe, Equiv.invFun_as_coe, 
               OrderIso.toEquiv_symm, RelIso.coe_fn_toEquiv, 
               comp_apply, OrderIso.le_iff_le]
    apply hf.1
    rw [←ord1.map_rel_iff']; simp; exact le
  constructor
  · intro b
    change b1.l b = b2.l (ord2.toFun (f ((ord1.symm.toFun) b)))
    rw [←lab2 (f (ord1.symm.toEquiv.toFun b))]
    rw [←hf.2.1, lab1 (ord1.symm.toEquiv.toFun b)]
    simp
  · simp only [Equiv.toFun_as_coe, RelIso.coe_fn_toEquiv, Equiv.invFun_as_coe,
               OrderIso.toEquiv_symm, EmbeddingLike.comp_injective, 
               EquivLike.injective_comp]
    exact hf.2.2

-- Well-definedness of ≤ for lpos on the Quotient. 
lemma le_wd (a1 a2 b1 b2 : LPO lab) (eqv1 : a1 ≈ b1)
(eqv2 : a2 ≈ b2) : (a1 ≤ a2) = (b1 ≤ b2) := by 
  ext; constructor
  · exact equiv_equiv_mono a1 a2 b1 b2 eqv1 eqv2
  · exact equiv_equiv_mono b1 b2 a1 a2 (Setoid.symm eqv1) (Setoid.symm eqv2)

end LPO 

variable {lab : Type}

-- For any LPO t that is ≤ a singleton, if it has an event (x : t.t),
-- then it must be isomorphic to the singleton. 
lemma any_le_action {t : LPO lab} {l : lab} 
(le : t ≤ action l) (x : t.t) : t ≈ action l := by
  obtain ⟨f, hf⟩ := le
  constructor; tauto
  have h : ∀ a : t.t, a = x
  · intro a
    have ha : f a = Node.mk; cases (f a); rfl
    have hx : f x = Node.mk; cases (f x); rfl
    rw [←hx] at ha; exact hf.2.2 ha
  fconstructor
  · exact { 
      toFun := f,
      invFun := λ _ => x,
      left_inv := by 
        dsimp only [LeftInverse]
        intro a; specialize h a; exact h.symm
      right_inv := by
        dsimp only [Function.RightInverse]
        dsimp only [LeftInverse]
        intro a; cases a; cases (f x); rfl
      map_rel_iff' := by
        intro a b; constructor
        all_goals
          intro le; simp at *
          have ha := h a
          have hb := h b
          rw [←hb] at ha
          subst ha; simp
      }
  · intro p; simp
    exact hf.2.1 p

-- A singleton QLPO 
@[simp]
def qaction (s : lab) : QLPO lab := ⟦action s⟧

namespace QLPO

-- Defines non-empty qlpos 
def inhab {l : LPO lab} (q : QLPO lab) (_ : q = ⟦l⟧) :=
Inhabited l.t  

-- The ≤ relation on qlpos 
def le (l1 l2 : QLPO lab) : Prop :=
Quotient.lift₂ (@LPO.le lab) LPO.le_wd l1 l2

-- ≤ is reflexive 
lemma refl (q1 : QLPO lab) : QLPO.le q1 q1 := by 
  refine Quotient.inductionOn q1 le_refl

-- ≤ is transitive 
lemma trans (q1 q2 q3 : QLPO lab) 
(le1 : QLPO.le q1 q2) (le2 : QLPO.le q2 q3) :
QLPO.le q1 q3 := by
  revert le1 le2
  refine Quotient.inductionOn₃ q1 q2 q3 LPO.le_trans

-- Since ≤ is reflexive and transitive it forms a Preorder. 
-- We should be able to prove that ≤ is antisymmetric and promote 
-- this to a partial order, but it's not needed. 
instance Preorder : Preorder (QLPO lab) :=
{ le := QLPO.le,
  le_refl := QLPO.refl,
  le_trans := QLPO.trans,
}

-- For some reason Lean can't infer that ≤ applies to equivalence 
-- classes of lpos, i.e., that ⟦l1⟧ ≤ ⟦l2⟧ is well-typed. So we tell it so. 
instance LE (lab : Type): LE (Quotient (@LPO.Setoid lab)) := ⟨QLPO.le⟩

-- API for ≤ applied to equivalence classes 
lemma le_iff {l1 l2 : LPO lab} : (⟦l1⟧ : QLPO lab) ≤ ⟦l2⟧ ↔ l1 ≤ l2 := by rfl 

-- Lift merge of lpos to the equivalence class of the merge
def merge_aux (l1 l2 : LPO lab) : QLPO lab := ⟦LPO.merge l1 l2⟧

lemma mine (l1 l2 : LPO lab) : l1 ≃ₑ l2 → (⟦l1⟧ : QLPO lab) = ⟦l2⟧ := by
  intro eqv 
  exact Quotient.eq.mpr (Exists.intro eqv rfl)

-- Show merge_aux is well-defined on the Quotient
lemma merge_aux_wd (a1 a2 b1 b2: LPO lab) (eqv1 : a1 ≈ b1) 
(eqv2 : a2 ≈ b2) : merge_aux a1 a2 = merge_aux b1 b2 := by
  obtain ⟨⟨ord1, lab1⟩, h1⟩ := eqv1
  obtain ⟨⟨ord2, lab2⟩, h2⟩ := eqv2
  clear h1 h2
  unfold merge_aux; apply Quotient.eq.mpr
  constructor; triv
  exact 
  { order := 
    { toFun := by
        intro x; rcases x with x | x
        · exact (.inl (ord1.toFun x))
        · exact (.inr (ord2.toFun x))
      invFun := by
        intro x; rcases x with x | x
        · exact (.inl (ord1.invFun x))
        · exact (.inr (ord2.invFun x))
      left_inv := by intros x; cases x; simp; simp 
      right_inv := by intros x; cases x; simp; simp 
      map_rel_iff' := by
        intro x y
        cases x with
        | inl x => cases y with
          | inl y => 
            simp 
            rw [Sum.inl_le_inl_iff, Sum.inl_le_inl_iff]
            exact OrderIso.le_iff_le ord1
          | inr y => simp; constructor <;> intro h <;> cases h
        | inr x => cases y with 
          | inl y => simp; constructor <;> intro h <;> cases h
          | inr y =>
            simp
            rw [Sum.inr_le_inr_iff, Sum.inr_le_inr_iff]
            exact OrderIso.le_iff_le ord2
    }
    label := by 
      intro p; rcases p with p | p; simp; exact lab1 p
      exact lab2 p
  }

-- Defines merge for QLPO
def merge (l1 l2 : QLPO lab) : QLPO lab :=
Quotient.lift₂ (@merge_aux lab) merge_aux_wd l1 l2

-- Notation for merge. 
infix:51 " ⊎ " => merge

namespace merge
-- Lift basic results about merge from lpos to qlpos 

lemma le_left {q1 q2 : QLPO lab} : q1 ≤ q1 ⊎ q2 := by
  exact Quotient.inductionOn₂ q1 q2 (@LPO.merge.le_left lab)

lemma le_right {q1 q2 : QLPO lab} : q2 ≤ q1 ⊎ q2 := by
  exact Quotient.inductionOn₂ q1 q2 (@LPO.merge.le_right lab)

def assoc (q1 q2 q3 : QLPO lab) :
 (q1 ⊎ q2) ⊎ q3 = q1 ⊎ (q2 ⊎ q3) := by
  refine Quotient.inductionOn₃ q1 q2 q3 fun
  | a, b, c => by 
    simp [merge, merge_aux]; 
    apply Quotient.eq.mpr
    exact LPO.merge.assoc' a b c

def comm (q1 q2 : QLPO lab):
q1 ⊎ q2 = q2 ⊎ q1 := by 
  refine Quotient.inductionOn₂ q1 q2 fun
  | a, b => by
    simp [merge, merge_aux]
    apply Quotient.eq.mpr 
    exact LPO.merge.comm' a b 

-- Distributiviey for the equivalence class notation over merge. 
lemma lpo_merge {l1 l2 : LPO lab} :
⟦LPO.merge l1 l2⟧ = ⟦l1⟧ ⊎ ⟦l2⟧ := by 
  simp [merge, merge_aux]

lemma merge_merge_le {q1 q2 q3 q4 : QLPO lab} (le1 : q1 ≤ q3)
(le2 : q2 ≤ q4) : q1 ⊎ q2 ≤ q3 ⊎ q4 := by 
  revert le1 le2
  refine Quotient.inductionOn₃ q1 q2 q3 fun
  | a, b, c => by 
    refine Quotient.inductionOn q4 fun
    | _ => by
      exact LPO.merge.merge_merge_le

lemma le_left_or_right_of_singleton {l1 : lab} {q2 q3 : QLPO lab} 
(le : qaction l1 ≤ q2 ⊎ q3) : qaction l1 ≤ q2 ∨ qaction l1 ≤ q3 := by
  revert le; simp [qaction]
  refine Quotient.inductionOn₂ q2 q3 fun
  | a, b => by
    clear q2 q3
    intro le
    rcases le with ⟨f, _, hf2, _⟩
    have im : (∃ v, (f Node.mk = .inl v)) ∨ (∃ v, (f Node.mk = .inr v))
    · rcases (f Node.mk); tauto; tauto
    cases im with 
    | inl im => 
      obtain ⟨val, hval⟩ := im; left; use λ _ => val
      constructor
      · intros p1 p2 le; cases le; simp
      constructor
      · intro p; cases p; simp
        change (action l1).l Node.mk = (a.merge b).l (.inl val)
        rw [←hval]
        exact hf2 Node.mk
      · intro a b h; cases a; cases b; rfl
    | inr im => 
      obtain ⟨val, hval⟩ := im; right; use λ _ => val
      constructor
      · intros p1 p2 le; cases le; simp
      constructor
      · intro p; cases p; simp
        change (action l1).l Node.mk = (a.merge b).l (.inr val)
        rw [←hval]; exact hf2 Node.mk
      · intro a b h; cases a; cases b; rfl

lemma any_le_qaction {t : QLPO lab} {l : lab}
{l1 : LPO lab} (eq : t = ⟦l1⟧) (inh : Inhabited l1.t)
(le : t ≤ qaction l) : t = qaction l := by 
  rw [eq] at le
  have e := any_le_action le
  haveI := inh
  specialize e default
  have : ⟦l1⟧ = ⟦action l⟧ := Quotient.eq.mpr e
  rw [eq]; exact this

lemma qaction_le_merge {t1 t2 : QLPO lab} {l : lab}
(le : qaction l ≤ t1 ⊎ t2) : qaction l ≤ t1 ∨ qaction l ≤ t2 := by
  revert le
  refine Quotient.inductionOn₂ t1 t2 fun
  | a, b => by
    clear t1 t2
    intro le
    replace le := LPO.merge.action_le_merge le
    cases le; tauto; tauto

lemma le_merge_of_le_left {q1 q2 q3 : QLPO lab}
(le : q1 ≤ q2) : q1 ≤ q2.merge q3 := by
  revert le
  refine Quotient.inductionOn₃ q1 q2 q3 fun
  | a, b, c => by
    clear q1 q2 q3
    intro le
    exact LPO.merge.le_merge_of_le_left le

lemma le_merge_of_le_right {q1 q2 q3 : QLPO lab}
(le : q1 ≤ q3) : q1 ≤ q2.merge q3 := by 
  revert le
  refine Quotient.inductionOn₃ q1 q2 q3 fun
  | a, b, c => by
    clear q1 q2 q3
    intro le
    exact LPO.merge.le_merge_of_le_right le

-- The merge of two non-empty lpos is not ≤ a singleton
lemma inhabited_merge_nle_singleton {l1 : lab} {l2 l3 : LPO lab}
(i2 : Inhabited l2.t) (i3 : Inhabited l3.t)
(le : l2.merge l3 ≤ action l1) : false := by 
  have a := i2.default
  have b := i3.default
  obtain ⟨f, hf⟩ := le
  have ninj : f (.inl a) = f (.inr b)
  · cases f (.inl a); cases f (.inr b); rfl
  replace ninj := hf.2.2 ninj
  cases ninj

end merge 

-- Lift Earlier to the equivalence class 
def earlier_aux (l1 l2 : LPO lab) : QLPO lab := ⟦LPO.earlier l1 l2⟧

-- Show Earlier is well-defined on the Quotient 
lemma earlier_aux_wd (a1 a2 b1 b2: LPO lab) (eqv1 : a1 ≈ b1) 
(eqv2 : a2 ≈ b2) : earlier_aux a1 a2 = earlier_aux b1 b2 := by
  rcases eqv1 with ⟨⟨ord1, lab1⟩, h1⟩
  rcases eqv2 with ⟨⟨ord2, lab2⟩, h2⟩
  clear h1 h2
  simp [earlier_aux];
  apply Quotient.eq.mpr
  constructor; triv
  exact 
  { order := 
    { toFun := by 
        intro x; cases x with
        | inl x => exact (.inl (ord1.toFun x))
        | inr x => exact (.inr (ord2.toFun x))
      invFun := by
        intro x; cases x with 
        | inl x => exact (.inl (ord1.invFun x))
        | inr x => exact (.inr (ord2.invFun x))
      left_inv := by intro x; cases x <;> simp 
      right_inv := by intro x; cases x <;> simp
      map_rel_iff' := by
        intro x y
        cases x with 
        | inl x => cases y with 
          | inl y => 
            simp
            change toLex (Sum.inl (ord1 x)) ≤ toLex (Sum.inl (ord1 y)) ↔ 
               toLex (Sum.inl x) ≤ toLex (Sum.inl y)
            simp
          | inr y => 
            simp
            change toLex (Sum.inl (ord1 x)) ≤ toLex (Sum.inr (ord2 y)) ↔ 
               toLex (Sum.inl x) ≤ toLex (Sum.inr y)
            simp
        | inr x => cases y with 
          | inl y => 
            simp
            change toLex (Sum.inr (ord2 x)) ≤ toLex (Sum.inl (ord1 y)) ↔ 
               toLex (Sum.inr x) ≤ toLex (Sum.inl y)
            simp
          | inr y => 
            simp
            change toLex (Sum.inr (ord2 x)) ≤ toLex (Sum.inr (ord2 y)) ↔ 
               toLex (Sum.inr x) ≤ toLex (Sum.inr y)
            simp
    }
    label := by intro p; rcases p with p | p; simp; exact lab1 p; exact lab2 p
  }

-- Define earlier for qlpos 
def earlier (q1 q2 : QLPO lab) :=
Quotient.lift₂ (@earlier_aux lab) earlier_aux_wd q1 q2

-- Notation for earlier 
infix:51 " ▷ " => earlier

namespace Earlier
-- Lift basic results about earlier to qlpos 

lemma le_left {q1 q2 : QLPO lab} : q1 ≤ q1 ▷ q2 := by 
  exact Quotient.inductionOn₂ q1 q2 (@LPO.Earlier.le_left lab)

lemma le_right {q1 q2 : QLPO lab} : q2 ≤ q1 ▷ q2 := by
  exact Quotient.inductionOn₂ q1 q2 (@LPO.Earlier.le_right lab)

lemma assoc (q1 q2 q3 : QLPO lab) :
(q1 ▷ q2) ▷ q3 = q1 ▷ (q2 ▷ q3) := by
  refine Quotient.inductionOn₃ q1 q2 q3 fun
  | a, b, c => by
    simp [earlier, earlier_aux]
    apply Quotient.eq.mpr
    exact LPO.Earlier.assoc' a b c

lemma earlier_earlier_le {q1 q2 q3 q4 : QLPO lab} (le1 : q1 ≤ q3)
(le2 : q2 ≤ q4) : q1 ▷ q2 ≤ q3 ▷ q4 := by 
  revert le1 le2
  refine Quotient.inductionOn₃ q1 q2 q3 fun
  | a, b, c => by
    refine Quotient.inductionOn q4 fun
  | _ => by 
    exact LPO.Earlier.earlier_earlier_le 

lemma inhabited_earlier_nle_singleton {l1 : lab} {l2 l3 : LPO lab}
(i2 : Inhabited l2.t) (i3 : Inhabited l3.t)
(le : l2.earlier l3 ≤ action l1) : false := by
  have a := i2.default
  have b := i3.default
  obtain ⟨f, hf⟩ := le
  have ninj : f (.inl a) = f (.inr b)
  · cases f (.inl a); cases f (.inr b); rfl
  replace ninj := hf.2.2 ninj
  cases ninj

end Earlier 

-- Distributive product of sets of qlpos 
def distributive_prod (S1 S2 : Set (QLPO lab)) :=
{ q : QLPO lab | ∃ q1 q2, q1 ∈ S1 ∧ q2 ∈ S2 ∧ q = q1 ⊎ q2 }

-- Notation for distributive product
infix:51 (priority := high) " ⋈ " => distributive_prod 

-- The merge of two things respectivly in S and T is in S ⋈ T 
lemma merge_mem_dist_prod {q1 q2 : QLPO lab} {S T : Set (QLPO lab)} 
(mem1 : q1 ∈ S) (mem2 : q2 ∈ T) : q1 ⊎ q2 ∈ S ⋈ T := by
  simp [distributive_prod]
  use q1, mem1
  use q2, mem2

-- API for working with ⋈ 
lemma mem_dist_prod_iff {l1 : LPO lab} {S T : Set (QLPO lab)} :
⟦l1⟧ ∈ S ⋈ T ↔ ∃ la lb, ⟦l1⟧ = ⟦la⟧ ⊎ ⟦lb⟧ ∧ ⟦la⟧ ∈ S ∧ 
⟦lb⟧ ∈ T := by 
 constructor
 · intro mem
   rcases mem with ⟨qa, qb, h1, h2, h3⟩
   revert h1 h2 h3
   refine Quotient.inductionOn₂ qa qb fun
   | a, b => by
     intro h1 h2 h3
     use a, b, h3, h1, h2
 · rintro ⟨la, lb, h1, h2, h3⟩
   rw [h1]; exact merge_mem_dist_prod h2 h3

-- ⋈ is associative 
lemma dist_prod_assoc {S T U : Set (QLPO lab)} :
(S ⋈ T) ⋈ U = S ⋈ (T ⋈ U) := by
  ext stu
  simp [(· ⋈ ·)]
  constructor
  · rintro ⟨st, ⟨s, hs1, ⟨t, ht1, hst⟩⟩, u, hu1, hstu⟩
    use s, hs1, (t ⊎ u); constructor
    · use t, ht1, u 
    · rw [hstu, hst]
      exact merge.assoc s t u
  · rintro ⟨s, hs1, tu, ⟨t, ht1, ⟨u, hu1, htu⟩⟩, hstu⟩
    use (s ⊎ t); constructor
    · use s, hs1, t, ht1
    · use u, hu1
      rw [hstu, htu]
      exact (merge.assoc s t u).symm

-- ⋈ is commutative 
lemma dist_prod_comm {S T : Set (QLPO lab)} : 
S ⋈ T = T ⋈ S := by
  ext st; simp [distributive_prod]
  constructor
  · rintro ⟨s, hs, t, ht, hst⟩
    use t, ht, s, hs
    rw [hst]; exact merge.comm s t
  · rintro ⟨t, ht, s, hs, hts⟩
    use s, hs, t, ht
    rw [hts]; exact merge.comm t s

-- Sequential composition of sets of qlpos 
def seq_comp (S1 S2 : Set (QLPO lab)) := 
{ q : QLPO lab | ∃ q1 q2, q1 ∈ S1 ∧ q2 ∈ S2 ∧ q = q1 ▷ q2 }

-- Notation for sequential composition 
infix:51 " ↝ " => seq_comp

-- The Earlier of two things respectively in S and T is in S ↝ T 
lemma earlier_mem_seq_comp {q1 q2 : QLPO lab} {S T : Set (QLPO lab)}
(mem1 : q1 ∈ S) (mem2 : q2 ∈ T) : q1 ▷ q2 ∈ S ↝ T := by
  simp [(· ↝ ·)]
  use q1, mem1
  use q2, mem2

-- ↝ is associative 
def seq_comp_assoc {S T U : Set (QLPO lab)} :
(S ↝ T) ↝ U = S ↝ (T ↝ U) := by
  ext stu;
  simp [(· ↝ ·)]
  constructor
  · rintro ⟨st, ⟨s, hs, ⟨t, ht, hst⟩⟩, ⟨u, hu, hstu⟩⟩
    use s, hs, (t ▷ u); constructor
    · use t, ht, u, hu
    rw [hstu, hst]
    exact Earlier.assoc s t u
  · rintro ⟨s, hs, tu, ⟨⟨t, ht, ⟨u, hu, htu⟩⟩, hstu⟩⟩
    use (s ▷ t); constructor
    · use s, hs, t, ht 
    · use u, hu
      rw [hstu, htu]
      exact (Earlier.assoc s t u).symm

-- API for working with ↝ 
lemma mem_seq_comp_iff {l : LPO lab} {S T : Set (QLPO lab)}:
⟦l⟧ ∈ S ↝ T ↔ ∃ la lb, ⟦l⟧ = ⟦la⟧ ▷ ⟦lb⟧ ∧ ⟦la⟧ ∈ S ∧ ⟦lb⟧ ∈ T := by
  constructor
  · intro mem
    rcases mem with ⟨qa, qb, h1, h2, h3⟩
    revert h1 h2 h3
    refine Quotient.inductionOn₂ qa qb fun
    | la, lb => by
      intro h1 h2 h3
      use la, lb, h3, h1, h2
  · rintro ⟨la, lb, h1, h2, h3⟩
    rw [h1]; simp [(· ↝ ·)]
    use ⟦la⟧, h2, ⟦lb⟧, h3

end QLPO 
