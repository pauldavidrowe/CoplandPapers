import CoplandPapers.OnOrderings.QLPO

open Function 

-- Notation for an order ideal (lower closure)
prefix:85 "ι" => lowerClosure 

-- Notation for an order filter (upper closure)
prefix:85 "φ" => upperClosure 

section Union_Laws

namespace QLPO
variable {lab : Type}
/- 
  In this section we prove Lemmas 1.1 and 2.1 from
  the JDG Fest paper. Namely,
  ι(S ∪ T) = ι(S) ∪ ι(T) and 
  φ(S ∪ T) = φ(S) ∪ φ(T). 
-/

instance LowerSet.instUnionLowerSet : Union (LowerSet (QLPO lab)) where 
  union := λ x y => 
    { carrier := x.carrier ∪ y.carrier  
      lower' := by 
        intro a b le mem
        cases mem with
        | inl mem => left; apply x.lower' le mem
        | inr mem => right; apply y.lower' le mem
    }
    
instance UpperSet.instUnionUpperSet : Union (UpperSet (QLPO lab)) where
  union := λ x y => 
    { carrier := x.carrier ∪ y.carrier 
      upper' := by
        intro a b le mem
        cases mem with 
        | inl mem => left; apply x.upper' le mem
        | inr mem => right; apply y.upper' le mem
    }

-- Lemma 1.1 from JDG Fest 
lemma lower_union (S T : Set (QLPO lab)) :
((ι (S ∪ T)) : Set (QLPO lab)) = (ι S) ∪ (ι T) := by 
  simp [(ι ·)]
  ext x; constructor
  · simp; intro y mem le
    cases mem with 
    | inl mem => left; simp; use y
    | inr mem => right; simp; use y 
  · simp; intro mem
    cases mem with 
    | inl mem =>
      simp at mem
      obtain ⟨a, ha⟩ := mem
      use a; tauto
    | inr mem => 
      simp at mem
      obtain ⟨a, ha⟩ := mem 
      use a; tauto

-- Lemma 2.1 from JDG Fest 
lemma upper_union (S T : Set (QLPO lab)) : (φ (S ∪ T)) = (φ S) ∪ (φ T) := by 
  simp [(φ ·)]
  ext x; constructor
  · simp; intro y mem le
    cases mem with 
    | inl mem => left; simp; use y 
    | inr mem => right; simp; use y
  · simp; intro mem
    cases mem with 
    | inl mem => 
      simp at mem
      obtain ⟨a, ha⟩ := mem
      use a; tauto
    | inr mem => 
      simp at mem
      obtain ⟨a, ha⟩ := mem
      use a; tauto

end QLPO
end Union_Laws

section Distributive_Product_Laws
/- 
  In this section we prove Lemmas 1.2 and 2.2 from the
  JDG Fest paper. Namely,
  ι(S ⋈ T) = ι(S) ⋈ ι(T) and 
  φ(S ⋈ T) = φ(φ(S) ⋈ φ(T)).

  The first equation takes a surprising amount of work!
  The issue is that it seems as though the only way to 
  prove it is do decompose any X ∈ ι(S ⋈ T) into X1 ⊎ X2. 
  This requires definitions of X1 and X2 based on the 
  function from X to some S ⊎ T (as, say, the preimages
  of elements in S and T respectively). Then we have to
  prove that X is indeed equal to the disjoint union
  of X1 and X2. This all gets more complicated with our
  definition of lpos which each have thier own underlying
  carrier type. 

  It would probably be easier to prove 
  ι(S ⋈ T) = ι(ι(S) ⋈ ι(T)). The difficulty essentially 
  amounts to showing that ι(S) ⋈ ι(T) is already a 
  lower set. This also might be sufficient for the purposes 
  of the main results, but we may as well prove the stronger
  fact. 
-/

namespace LPO.merge 
open LPO 
variable {lab : Type}

-- The pre-image of the left half of a merge. It's non-computable because
-- we know such a pre-image exists, but we do not provide a way to construct it
noncomputable
def left_preim {a b c : LPO lab} (f : a.t → (merge b c).t) (_ : LPO.hom f) : LPO lab :=
{ t := { ab : a.t × b.t // f ab.1 = (.inl ab.2) }
  fin := Fintype.ofFinite { ab : a.t × b.t // f ab.fst = .inl ab.snd }
  po := 
  { le := λ p1 p2 => p1.val.fst ≤ p2.val.fst
    lt := λ p1 p2 => p1.val.fst < p2.val.fst
    le_refl := by simp
    le_trans := by
      intro a b c ab bc
      simp at *; exact ge_trans bc ab 
    lt_iff_le_not_le := by 
      intro a b; exact lt_iff_le_not_le
    le_antisymm := by
      intro a b ab ba 
      rcases a with ⟨⟨a1, b1⟩, h1⟩
      rcases b with ⟨⟨a2, b2⟩, h2⟩
      simp at *
      constructor
      · exact PartialOrder.le_antisymm a1 a2 ab ba
      · have : a1 = a2 := PartialOrder.le_antisymm a1 a2 ab ba
        subst this
        simp at h1 h2; rw [h2] at h1; cases h1; rfl
  }
  l := λ px => a.l px.1.1
}

-- Analogously, this is the pre-image of the right half of a merge. 
noncomputable
def right_preim {a b c : LPO lab} (f : a.t → (merge b c).t) (_ : LPO.hom f) : LPO lab :=
{ t := { ac : a.t × c.t // f ac.1 = (.inr ac.2) },
  fin := Fintype.ofFinite {ac : a.t × c.t  // f ac.1 = .inr ac.2},
  po := 
  { le := λ p1 p2 => p1.1.1 ≤ p2.1.1
    lt := λ p1 p2 => p1.1.1 < p2.1.1
    le_refl := by simp
    le_trans := by 
      intro a b c ab bc
      simp at *; exact ge_trans bc ab 
    lt_iff_le_not_le := by 
      intro a b; exact lt_iff_le_not_le
    le_antisymm := by 
      intro a b ab ba 
      rcases a with ⟨⟨a1, b1⟩, h1⟩
      rcases b with ⟨⟨a2, b2⟩, h2⟩
      simp at *
      constructor
      · exact PartialOrder.le_antisymm a1 a2 ab ba
      · have : a1 = a2 := PartialOrder.le_antisymm a1 a2 ab ba
        subst this
        simp at h1 h2; rw [h2] at h1; cases h1; rfl
  },
  l := λ px => a.l px.1.1, 
}

-- API of simp lemmas for the above definitions 
@[simp]
lemma left_preim_le_def {a b c : LPO lab} (f : a.t → (merge b c).t) (hf : LPO.hom f) 
(x1 x2 : (left_preim f hf).t) : 
x1 ≤ x2 ↔ x1.1.1 ≤ x2.1.1 := by rfl

@[simp]
lemma right_preim_le_def {a b c : LPO lab} (f : a.t → (merge b c).t) (hf : LPO.hom f) 
(x1 x2 : (right_preim f hf).t) : 
x1 ≤ x2 ↔ x1.1.1 ≤ x2.1.1 := by rfl 

@[simp]
lemma left_preim_label {a b c : LPO lab} (f : a.t → (merge b c).t) (hf : LPO.hom f) 
(x : (left_preim f hf).t) :
(left_preim f hf).l x = a.l x.1.1 := by rfl 

@[simp]
lemma right_preim_label {a b c : LPO lab} (f : a.t → (merge b c).t) (hf : LPO.hom f) 
(x : (right_preim f hf).t) :
(right_preim f hf).l x = a.l x.1.1 := by rfl 

-- The left pre-image of a merge is ≤ the merge 
lemma left_preim_le {a b c : LPO lab} (f : a.t → (merge b c).t) (hf : LPO.hom f) :
left_preim f hf ≤ b := by
  use λ pab => pab.1.2
  constructor
  · simp; intro p1 p2 le
    rcases p1 with ⟨⟨pa1, pb1⟩, h1⟩
    rcases p2 with ⟨⟨pa2, pb2⟩, h2⟩
    simp at h1 h2 le ⊢
    replace le := hf.1 le; rw [h1, h2] at le
    exact Sum.inl_le_inl_iff.1 le
  constructor
  · simp; rintro ⟨⟨pa, pb⟩, h⟩
    simp at *; rw [hf.2.1 pa, h]
    apply merge.label_inl
  · intro x y eq; simp at *
    apply Subtype.eq 
    have hx := x.2
    have hy := y.2
    --simp at *; 
    rw [eq] at hx 
    rw [←hy] at hx
    apply hf.2.2 at hx 
    exact Prod.ext hx eq

-- The right pre-image of a merge is ≤ the merge 
lemma right_preim_le {a b c : LPO lab} (f : a.t → (merge b c).t) (hf : LPO.hom f) :
right_preim f hf ≤ c := by
  use λ pac => pac.1.2
  constructor
  · simp; intro p1 p2 le
    rcases p1 with ⟨⟨pa1, pb1⟩, h1⟩
    rcases p2 with ⟨⟨pa2, pb2⟩, h2⟩
    simp at h1 h2 le ⊢
    replace le := hf.1 le; rw [h1, h2] at le
    exact Sum.inr_le_inr_iff.1 le
  constructor 
  · simp; rintro ⟨⟨pa, pb⟩, h⟩
    simp at *; rw [hf.2.1 pa, h] 
    apply merge.label_inr
  · intro x y eq; simp at *
    apply Subtype.eq
    have hx := x.2
    have hy := y.2
    rw [eq] at hx 
    rw [←hy] at hx
    apply hf.2.2 at hx
    exact Prod.ext hx eq

-- Since merge s t is only isomorphic and not equal to the merge of 
-- the pre-images, we have to construct the function into the merge
-- of the pre-images given the original function. 
def quasi_id {x s t : LPO lab} {f : x.t → (merge s t).t} (hf : LPO.hom f) :
x.t → (merge (left_preim f hf) (right_preim f hf)).t :=
λ px => 
  let bc := (f px)
  let h : (f px) = bc := rfl
  match bc, h with 
  | (.inl b), h => (.inl ⟨(px, b), h⟩)
  | (.inr c), h => (.inr ⟨⟨px, c⟩, h⟩)

-- API to work with the above definition 
lemma quasi_id_left {x s t : LPO lab} {f : x.t → (merge s t).t} 
(hf : LPO.hom f) (px : x.t) (ps : s.t) (hpb : f px = .inl ps ) :
quasi_id hf px = .inl ⟨(px, ps), hpb⟩ := by 
  simp [quasi_id]
  split
  case h_1 a b c eq1 eq2 _ 
  · congr
    rw [hpb] at eq1
    apply Sum.inl_injective at eq1
    symm; exact eq1
  · simp_all only [heq_eq_eq]

lemma quasi_id_right {x s t : LPO lab} {f : x.t → (merge s t).t} 
(hf : LPO.hom f) (px : x.t) (pt : t.t) (hpb : f px = .inr pt ) :
quasi_id hf px = .inr ⟨⟨px, pt⟩, hpb⟩ := by
  simp [quasi_id]
  split
  case h_1 a b c eq1 eq2 _ 
  · simp_all only [heq_eq_eq] 
  case h_2 a b c eq1 eq2 bc 
  · congr
    rw [hpb] at eq1
    apply Sum.inr_injective at eq1
    symm; exact eq1

-- Shows that the original LPO is isomorphic to the merge of the
-- left and right pre-images, and hence they are equal as qlpos 
lemma split {x1 s t : LPO lab} (f : x1.t → (s.merge t).t) 
(hf : LPO.hom f) :
⟦x1⟧ = ⟦LPO.merge.left_preim f hf⟧ ⊎ ⟦LPO.merge.right_preim f hf⟧ := by 
  rw [←QLPO.merge.lpo_merge]; simp; symm
  constructor; triv
  exact 
  { order := 
    { toFun := by
        intro pab
        rcases pab with pab | pab; exact pab.1.1; exact pab.1.1
      invFun := quasi_id hf
      left_inv := by 
        intro pbc; cases pbc with 
        | inl pbc => 
          rcases pbc with ⟨⟨pb, ps⟩, hb⟩
          exact LPO.merge.quasi_id_left hf pb ps hb
        | inr pbc => 
          rcases pbc with ⟨⟨pc, ps⟩, hc⟩
          exact LPO.merge.quasi_id_right hf pc ps hc
      right_inv := by 
        intro px
        have : (∃ ps, f px = .inl ps) ∨ (∃ pt, f px = .inr pt)
        · exact LPO.merge.inl_or_inr_of_lpo_hom px
        cases this with 
        | inl this =>
          obtain ⟨ps, hs⟩ := this
          have eq1 := LPO.merge.quasi_id_left hf px ps hs
          rw [eq1]
        | inr this =>
          obtain ⟨ps, hs⟩ := this
          have eq1 := LPO.merge.quasi_id_right hf px ps hs
          rw [eq1]
      map_rel_iff' := by 
        intro a b
        cases a with 
        | inl a => cases b with 
          | inl b => 
            rw [Sum.inl_le_inl_iff]; simp
          | inr b => 
            simp; constructor <;> intro le
            · apply hf.1 at le
              rcases a with ⟨⟨a, s⟩, ha⟩
              rcases b with ⟨⟨b, s⟩, hb⟩ 
              simp at le; rw [ha, hb] at le
              cases le
            · cases le
        | inr a => cases b with 
          | inl b => 
            simp; constructor <;> intro le
            · apply hf.1 at le
              rcases a with ⟨⟨a, s⟩, ha⟩
              rcases b with ⟨⟨b, s⟩, hb⟩ 
              simp at le; rw [ha, hb] at le
              cases le
            · cases le
          | inr b => 
            rw [Sum.inr_le_inr_iff]; simp
    }
    label := by 
      intro p; rcases p with p | p <;> { rcases p with ⟨⟨px, py⟩, hp⟩; simp }
  }

end LPO.merge  

namespace QLPO 
open merge 
variable {lab : Type}

-- The next two lemmas show that ι distributes over ⋈ 
lemma lower_dist_prod_mp (S T : Set (QLPO lab)) (x : QLPO lab) :
 x ∈ (ι (S ⋈ T)).1 → x ∈ (ι S).1 ⋈ (ι T).1 := by 
  rintro ⟨g, ⟨s, t, smem, tmem, eq⟩, xleg⟩
  revert smem tmem eq xleg
  refine Quotient.inductionOn₃ g s t fun
  | g, s, t => by
    refine Quotient.inductionOn x fun
    | x => by 
      intro xleg smem tmem eq
      rw [eq] at xleg
      obtain ⟨f, hf⟩ := xleg
      let xa : LPO lab := LPO.merge.left_preim f hf 
      let xb : LPO lab := LPO.merge.right_preim f hf 
      have : ⟦x⟧ = ⟦xa⟧ ⊎ ⟦xb⟧ := LPO.merge.split f hf
      rw [mem_dist_prod_iff]; use xa, xb, this
      constructor
      · simp [lowerClosure]
        rw [@Set.mem_setOf (QLPO lab)]
        use ⟦s⟧, smem
        rw [QLPO.le_iff]
        exact LPO.merge.left_preim_le f hf
      · simp [lowerClosure]
        rw [@Set.mem_setOf (QLPO lab)]
        use ⟦t⟧, tmem
        rw [QLPO.le_iff]
        exact LPO.merge.right_preim_le f hf

lemma lower_dist_prod_mpr  (S T : Set (QLPO lab)) (qx : QLPO lab) :
 qx ∈ ((ι S) : Set (QLPO lab)) ⋈ (ι T) → qx ∈ ι (S ⋈ T) := by
  rintro ⟨qgs, qgt, ⟨qs, smem, gles⟩, ⟨qt, tmem, glet⟩, xdef⟩
  revert smem gles tmem glet xdef
  refine Quotient.inductionOn₃ qgt qs qt fun 
  | gt, s, t => by
    refine Quotient.inductionOn₂ qx qgs fun
    | x, gs => by
      intro smem gles xdef tmem glet
      rw [xdef]; rw [QLPO.le_iff] at *
      simp; use (⟦s⟧ ⊎ ⟦t⟧)
      constructor; exact merge_mem_dist_prod smem tmem
      change LPO.merge gs gt ≤ LPO.merge s t
      obtain ⟨fs, hfs⟩ := gles
      obtain ⟨ft, hft⟩ := glet
      use LPO.merge.merge_le_merge_fun fs ft
      constructor
      · intro p1 p2 le
        cases p1 <;> cases p2
        · simp [LPO.merge.merge_le_merge_fun]
          rw [Sum.inl_le_inl_iff] at le ⊢
          exact hfs.1 le
        · cases le
        · cases le
        · simp [LPO.merge.merge_le_merge_fun]
          rw [Sum.inr_le_inr_iff] at le ⊢
          exact hft.1 le
      constructor
      · intro p; rcases p with p | p 
        · simp [LPO.merge.merge_le_merge_fun]
          exact hfs.2.1 p
        · simp [LPO.merge.merge_le_merge_fun]
          exact hft.2.1 p
      · intro p1 p2 peq
        cases p1 <;> cases p2
        · simp [LPO.merge.merge_le_merge_fun] at peq
          rw [Sum.inl.inj_iff] at *
          exact hfs.2.2 peq
        · cases peq
        · cases peq
        · simp [LPO.merge.merge_le_merge_fun] at peq
          rw [Sum.inr.inj_iff] at *
          exact hft.2.2 peq

-- Lemma 1.2 of JDG Fest
lemma lower_dist_prod (S T : Set (QLPO lab)) :
((ι (S ⋈ T)) : Set (QLPO lab)) = (ι S) ⋈ (ι T) := by 
  ext x; constructor
  · exact lower_dist_prod_mp S T x
  · exact lower_dist_prod_mpr S T x

-- The next two lemmas show how φ distributes over ⋈ 
lemma upper_dist_prod_mp (S T : Set (QLPO lab)) (X : QLPO lab) :
X ∈ φ  (S ⋈ T) → X ∈ φ (((φ S) : Set (QLPO lab)) ⋈ φ T) := by 
  rintro ⟨G, ⟨G1, ⟨G2, G1s, G2t, Geq⟩⟩, le⟩
  use (G1 ⊎ G2)
  constructor
  · suffices : G1 ∈ ↑(φ S) ∧ G2 ∈ ↑(φ T)
    · exact merge_mem_dist_prod this.1 this.2
    constructor
    · exact subset_upperClosure G1s
    · exact subset_upperClosure G2t
  · rw [←Geq]; exact le

lemma upper_dist_prod_mpr (S T : Set (QLPO lab)) (X : QLPO lab) :
X ∈ φ (((φ S) : Set (QLPO lab)) ⋈ φ T) → X ∈ φ (S ⋈ T) := by 
  rintro ⟨G, ⟨⟨G1, ⟨G2, h1, h2, Geq⟩⟩, le⟩⟩
  rcases h1 with ⟨H1, H1s, H1leG1⟩
  rcases h2 with ⟨H2, H2t, H2leG2⟩
  use H1 ⊎ H2
  constructor
  · exact merge_mem_dist_prod H1s H2t
  · apply le_trans _ _; use G1 ⊎ G2
    exact merge_merge_le H1leG1 H2leG2
    rw [←Geq]; exact le

-- Lemma 2.2 of JDG Fest 
lemma upper_dist_prod (S T : Set (QLPO lab)) : 
φ (S ⋈ T) = φ (φ S ⋈ φ T) := by 
  ext x; constructor
  · exact upper_dist_prod_mp S T x
  · exact upper_dist_prod_mpr S T x

end QLPO 

end Distributive_Product_Laws

section Sequential_Composition_Laws
/-
  In this section we prove Lemmas 1.3 and 2.3 from the
  JDG Fest paper. Namely,
  ι(S ↝ T) = ι(ι(S) ↝ ι(T)) and 
  φ(S ↝ T) = φ(φ(S) ↝ φ(T)).
-/
namespace QLPO 
variable {lab : Type}

-- The next two lemmas show how ι distributes over ↝ 
lemma lower_seq_comp_mp (S T : Set (QLPO lab)) (X : QLPO lab) :
X ∈ ι (S ↝ T) → X ∈ ι (((ι S) : Set (QLPO lab)) ↝ ι T) := by 
  rintro ⟨G, ⟨G1, G2, G1s, G2t, Geq⟩, XleG⟩
  use G1 ▷ G2
  constructor
  · apply earlier_mem_seq_comp
    exact subset_lowerClosure G1s
    exact subset_lowerClosure G2t
  · rw [←Geq]; exact XleG

lemma lower_seq_comp_mpr (S T : Set (QLPO lab)) (X : QLPO lab) :
X ∈ ι (((ι S) : Set (QLPO lab)) ↝ ι T) → X ∈ ι (S ↝ T) := by 
  rintro ⟨G, ⟨G1, ⟨G2, G1s, G2t, Geq⟩⟩, XleG⟩
  rcases G1s with ⟨H1, H1s, H1le⟩
  rcases G2t with ⟨H2, H2t, H2le⟩
  use H1 ▷ H2
  constructor
  · apply earlier_mem_seq_comp H1s H2t
  · rw [Geq] at XleG
    apply le_trans XleG
    exact Earlier.earlier_earlier_le H1le H2le

-- Lemma 1.3 of JDG Fest 
lemma lower_seq_comp (S T : Set (QLPO lab)) : 
ι (S ↝ T) = ι (ι S ↝ ι T) := by 
  ext X; constructor
  · exact lower_seq_comp_mp S T X
  · exact lower_seq_comp_mpr S T X

-- The next two lemmas show how φ distributes over ↝ 
lemma upper_seq_comp_mp (S T : Set (QLPO lab)) (X : QLPO lab) :
X ∈ φ (S ↝ T) → X ∈ φ (((φ S) : Set (QLPO lab)) ↝ φ T) := by 
  rintro ⟨G, ⟨G1, ⟨G2, G1s, G2t, Geq⟩⟩, Gle⟩
  use G1 ▷ G2
  constructor
  · apply earlier_mem_seq_comp
    exact subset_upperClosure G1s
    exact subset_upperClosure G2t
  · rw [←Geq]; exact Gle

lemma upper_seq_comp_mpr (S T : Set (QLPO lab)) (X : QLPO lab) : 
X ∈ φ (((φ S) : Set (QLPO lab)) ↝ φ T) → X ∈ φ (S ↝ T) := by 
  rintro ⟨G, ⟨G1, ⟨G2, G1s, G2s, Geq⟩⟩, Gle⟩
  rcases G1s with ⟨H1, H1s, H1le⟩
  rcases G2s with ⟨H2, H2t, H2le⟩
  use H1 ▷ H2
  constructor
  · exact earlier_mem_seq_comp H1s H2t
  · rw [Geq] at Gle
    apply le_trans _ Gle
    exact Earlier.earlier_earlier_le H1le H2le

-- Lemma 2.3 of JDG Fest 
lemma upper_seq_comp (S T : Set (QLPO lab)) :
φ (S ↝ T) = φ (φ S ↝ φ T) := by 
  ext X; constructor
  · exact upper_seq_comp_mp S T X
  · exact upper_seq_comp_mpr S T X

end QLPO
end Sequential_Composition_Laws 
