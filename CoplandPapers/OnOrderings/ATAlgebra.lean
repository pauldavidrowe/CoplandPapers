import CoplandPapers.OnOrderings.Supports
import CoplandPapers.OnOrderings.Covers 

/-  
  This file proves the algebraic facts about attack trees that
  are presented in the paper on attack tree specialization. 

  The results shown here are not part of the JDG Fest paper, 
  but they provide an alternative "aglebraic" semantics for attack
  trees that is essentially equivalent to the base semantics. 

  The results on inequalities require us to define functions that
  witness those inequalities. 
-/
namespace AT 
open AttackTree

section 
variable {lab : Type} {t u v w : AttackTree lab} 

lemma at_and_assoc : BS ((t.and u).and v) = BS (t.and (u.and v)) := by 
  simp; exact QLPO.dist_prod_assoc

lemma at_and_comm : BS (t.and u) = BS (u.and t) := by 
  simp; exact QLPO.dist_prod_comm

lemma at_or_assoc : BS ((t.or u).or v) = BS (t.or (u.or v)) := by
  simp; exact (BS t).union_assoc (BS u) (BS v)

lemma at_or_comm : BS (t.or u) = BS (u.or t) := by 
  simp; exact (BS t).union_comm (BS u)

lemma at_or_idempotent : BS (t.or t) = BS t := by simp

lemma at_and_distrib : BS ((t.or u).and v) = BS ((t.and v).or (u.and v)) := by 
  simp [(· ⋈ ·)]
  ext abc
  constructor
  · simp
    intro ab hab c hc habc
    cases hab with 
    | inl hab => left; use ab, hab, c, hc, habc
    | inr hab => right; use ab, hab, c, hc, habc
  · simp
    intro h
    cases h with 
    | inl h =>
      rcases h with ⟨a, ha, c, hc, hac⟩
      use a, .inl ha, c, hc, hac
    | inr h =>
      rcases h with ⟨b, hb, c, hc, hbc⟩
      use b, .inr hb, c, hc, hbc

lemma at_seq_assoc : BS ((t.seq u).seq v) = BS (t.seq (u.seq v)) := by 
  simp; exact QLPO.seq_comp_assoc

lemma at_seq_or_dist : BS (t.seq (u.or v)) = BS ((t.seq u).or (t.seq v)) := by 
  ext abc
  simp [(· ↝ ·)]
  constructor
  · rintro ⟨a, ha, uv, huv, habc⟩
    cases huv with 
    | inl huv => left; use a, ha, uv, huv, habc
    | inr huv => right; use a, ha, uv, huv, habc 
  · intro h
    cases h with 
    | inl h =>
      rcases h with ⟨a, ha, ⟨b, hb, hab⟩⟩
      use a, ha, b, .inl hb, hab
    | inr h =>
      rcases h with ⟨a, ha, ⟨c, hc, hac⟩⟩
      use a, ha, c, .inr hc, hac

lemma at_or_seq_dist : BS ((t.or u).seq v) = BS ((t.seq v).or (u.seq v)) := by
  ext abc
  simp [(· ↝ ·)]
  constructor
  · rintro ⟨ab, hab, c, hc, hac⟩
    cases hab with 
    | inl hab => left; use ab, hab, c, hc, hac
    | inr hab => right; use ab, hab, c, hc, hac
  · intro h
    cases h with 
    | inl h =>
      rcases h with ⟨a, ha, c, hc, hac⟩
      use a, .inl ha, c, hc, hac
    | inr h =>
      rcases h with ⟨b, hb, c, hc, hbc⟩
      use b, .inr hb, c, hc, hbc

section supports
namespace Supports 

-- What breaks here? 
--local attribute [reducible] Supports.AttSup Supports.CopSup
local instance : Preorder (AttackTree lab) := AT.supports_preorder lab

variable {lab : Type} {t u v w : AttackTree lab}

section and_seq_and

@[simp]
def and_seq_and_fun {T U V W : LPO lab} 
(x : ((T.earlier V).merge (U.earlier W)).t) : ((T.merge U).earlier (V.merge W)).t :=
match x with 
| (.inl (.inl t)) => .inl (.inl t)
| (.inl (.inr v)) => .inr (.inl v)
| (.inr (.inl u)) => .inl (.inr u)
| (.inr (.inr w)) => .inr (.inr w)


@[simp]
lemma asa_fun_ll {T U V W : LPO lab} {t : T.t} :
and_seq_and_fun ((.inl (.inl t)) : ((T.earlier V).merge (U.earlier W)).t) 
  = toLex (.inl (.inl t)) := by rfl

@[simp]
lemma asa_fun_lr {T U V W : LPO lab} (v : V.t) :
and_seq_and_fun ((.inl (.inr v)) : ((T.earlier V).merge (U.earlier W)).t) 
  = toLex (.inr (.inl v)) := by rfl

@[simp]
lemma asa_fun_rl {T U V W : LPO lab} (u : U.t) :
and_seq_and_fun ((.inr (.inl u)) : ((T.earlier V).merge (U.earlier W)).t) 
  = toLex (.inl (.inr u)) := by rfl

@[simp]
lemma asa_fun_rr {T U V W : LPO lab} (w : W.t) :
and_seq_and_fun ((.inr (.inr w)) : ((T.earlier V).merge (U.earlier W)).t) 
  = toLex (.inr (.inr w)) := by rfl


lemma and_seq_and_le  {T U V W : LPO lab} : 
(T.earlier V).merge (U.earlier W) ≤ (T.merge U).earlier (V.merge W) := by 
  use and_seq_and_fun
  constructor
  · intros p1 p2 le
    cases p1 with 
    | inl p1 => cases p2 with 
      | inl p2 => cases p1 with
        | inl p1 => cases p2 with
          | inl p2 =>
            simp
            rw [Sum.inl_le_inl_iff] at le
            apply Sum.Lex.inl_le_inl_iff.2
            apply Sum.inl_le_inl_iff.2
            exact Sum.Lex.inl_le_inl_iff.mp le
          | inr p2 =>
            apply Sum.Lex.inl_le_inr 
        | inr p1 => cases p2 with
          | inl p2 =>
            rw [Sum.inl_le_inl_iff] at le
            cases le
          | inr p2 =>
            simp
            rw [Sum.inl_le_inl_iff] at le
            apply Sum.Lex.inr_le_inr_iff.2
            apply Sum.inl_le_inl_iff.2
            exact Sum.Lex.inr_le_inr_iff.mp le
      | inr p2 => cases le
    | inr p1 => cases p2 with 
      | inl p2 => cases le
      | inr p2 => cases p1 with 
        | inl p1 => cases p2 with 
          | inl p2 =>
            simp
            rw [Sum.inr_le_inr_iff] at le
            apply Sum.Lex.inl_le_inl_iff.2 
            apply Sum.inr_le_inr_iff.2
            exact Sum.Lex.inl_le_inl_iff.mp le
          | inr p2 =>
            apply Sum.Lex.inl_le_inr 
        | inr p1 => cases p2 with
          | inl p2 =>
            rw [Sum.inr_le_inr_iff] at le
            cases le
          | inr p2 =>
            simp
            rw [Sum.inr_le_inr_iff] at le
            apply Sum.Lex.inr_le_inr_iff.2
            apply Sum.inr_le_inr_iff.2
            exact Sum.Lex.inr_le_inr_iff.mp le
  constructor
  · intro p
    rcases p with p | p <;> rcases p with p | p <;> simp
  · intro p1 p2 eq
    cases p1 with
    | inl p1 => cases p2 with 
      | inl p2 => cases p1 with
        | inl p1 => cases p2 with 
          | inl p2 => simp at *; cases eq; congr
          | inr p2 => simp at *
        | inr p1 => cases p2 with 
          | inl p2 => simp at *
          | inr p2 => simp at *; cases eq; congr
      | inr p2 => cases p1 with 
        | inl p1 => cases p2 with
          | inl p2 => simp at *; cases eq
          | inr p2 => simp at *
        | inr p1 => cases p2 with 
          | inl p2 => simp at *
          | inr p2 => simp at *; cases eq
    | inr p1 => cases p2 with 
      | inl p2 => cases p1 with 
        | inl p1 => cases p2 with
          | inl p2 => simp at *; cases eq
          | inr p2 => simp at *
        | inr p1 => cases p2 with 
          | inl p2 => simp at *
          | inr p2 => simp at *; cases eq
      | inr p2 => cases p1 with 
        | inl p1 => cases p2 with 
          | inl p2 => simp at *; cases eq; congr
          | inr p2 => simp at *
        | inr p1 => cases p2 with 
          | inl p2 => simp at *
          | inr p2 => simp at *; cases eq; congr

lemma and_seq_and_le'  {T U V W : QLPO lab} : 
(T ▷ V) ⊎ (U ▷ W) ≤ (T ⊎ U) ▷ (V ⊎ W) := by
  refine Quotient.inductionOn W fun
  | _ => by
    clear W
    refine Quotient.inductionOn₃ T U V fun 
    | t, u, v => by
      clear T U V
      use and_seq_and_fun
      constructor
      · intros p1 p2 le
        cases p1 with
        | inl p1 => cases p2 with 
          | inl p2 => cases p1 with
            | inl p1 => cases p2 with
              | inl p2 =>
                simp
                rw [Sum.inl_le_inl_iff] at le
                apply Sum.Lex.inl_le_inl_iff.2
                apply Sum.inl_le_inl_iff.2
                exact Sum.Lex.inl_le_inl_iff.mp le
              | inr p2 => exact Sum.Lex.sep (Sum.inl p1) (Sum.inl p2)
            | inr p1 => cases p2 with
              | inl p2 => 
                rw [Sum.inl_le_inl_iff] at le
                cases le
              | inr p2 => 
                simp
                rw [Sum.inl_le_inl_iff] at le
                apply Sum.Lex.inr_le_inr_iff.2
                apply Sum.inl_le_inl_iff.2
                exact Sum.Lex.inr_le_inr_iff.mp le
          | inr p2 => cases le
        | inr p1 => cases p2 with
          | inl p2 => cases le
          | inr p2 => cases p1 with 
            | inl p1 => cases p2 with
              | inl p2 =>
                simp
                rw [Sum.inr_le_inr_iff] at le
                apply Sum.Lex.inl_le_inl_iff.2
                apply Sum.inr_le_inr_iff.2
                exact Sum.Lex.inl_le_inl_iff.mp le
              | inr p2 => exact Sum.Lex.sep (Sum.inr p1) (Sum.inr p2)
            | inr p1 => cases p2 with 
              | inl p2 =>
                rw [Sum.inr_le_inr_iff] at le
                cases le
              | inr p2 =>
                simp
                rw [Sum.inr_le_inr_iff] at le
                apply Sum.Lex.inr_le_inr_iff.2
                apply Sum.inr_le_inr_iff.2
                exact Sum.Lex.inr_le_inr_iff.mp le
      constructor
      · intro p 
        rcases p with p | p <;> cases p <;> simp
      · intro p1 p2 eq
        cases p1 with
        | inl p1 => cases p2 with
          | inl p2 => cases p1 with
            | inl p1 => cases p2 with
              | inl p2 => simp at *; cases eq; congr 
              | inr p2 => simp at *
            | inr p1 => cases p2 with
              | inl p2 => simp at *
              | inr p2 => simp at *; cases eq; congr
          | inr p2 => cases p1 with
            | inl p1 => cases p2 with
              | inl p2 => simp at *; cases eq
              | inr p2 => simp at *
            | inr p1 => cases p2 with
              | inl p2 => simp at *
              | inr p2 => simp at *; cases eq
        | inr p1 => cases p2 with
          | inl p2 => cases p1 with 
            | inl p1 => cases p2 with
              | inl p2 => simp at *; cases eq
              | inr p2 => simp at *
            | inr p1 => cases p2 with
              | inl p2 => simp at *
              | inr p2 => simp at *; cases eq
          | inr p2 => cases p1 with 
            | inl p1 => cases p2 with
              | inl p2 => simp at *; cases eq; congr
              | inr p2 => simp at *
            | inr p1 => cases p2 with
              | inl p2 => simp at *
              | inr p2 => simp at *; cases eq; congr

lemma at_and_seq_and : ((t.and u).seq (v.and w)) ≤ (t.seq v).and (u.seq w) := by
  --rw supports.AttSup.le_def',
  intro H Hmem; simp [(· ⋈ ·), (· ↝ ·)] at *
  rcases Hmem with ⟨TU, ⟨T, hT, U, hU, hTU⟩, ⟨VW, ⟨V, hV, W, hW, hVW⟩, hTUVW⟩⟩
  use ((T ▷ V) ⊎ (U ▷ W))
  constructor
  · refine ⟨T ▷ V, ⟨T, hT, V, hV, by rfl⟩, ⟨U ▷ W, ⟨U, hU, W, hW, by rfl⟩, by rfl⟩⟩
  · rw [hTUVW, hTU, hVW]
    exact and_seq_and_le'

end and_seq_and 

section and_seq 

@[simp]
def and_seq_fun {T U W : LPO lab} (x : (T.merge (U.earlier W)).t) :
((T.merge U).earlier W).t :=
match x with 
| (.inl t) => .inl (.inl t)
| (.inr (.inl u)) => (.inl (.inr u))
| (.inr (.inr w)) => .inr w

lemma and_seq_le {T U W : LPO lab} : 
(T.merge (U.earlier W)) ≤ ((T.merge U).earlier W) := by
  use and_seq_fun
  constructor
  · intro p1 p2 le
    cases p1 with 
    | inl p1 => cases p2 with
      | inl p2 =>
        simp
        rw [Sum.inl_le_inl_iff] at le
        rw [←@Sum.inl_le_inl_iff T.t U.t _ _] at le
        apply Sum.Lex.inl_le_inl_iff.2 le
      | inr p2 => cases le
    | inr p1 => cases p2 with
      | inl p2 => cases le
      | inr p2 => cases p1 with
        | inl p1 => cases p2 with
          | inl p2 =>
            simp
            rw [Sum.inr_le_inr_iff] at le
            replace le := Sum.Lex.inl_le_inl_iff.1 le
            apply Sum.Lex.inl_le_inl_iff.2
            exact Sum.inr_le_inr_iff.2 le
          | inr p2 =>
            simp
            exact Sum.Lex.inl_le_inr _ _
        | inr p1 => cases p2 with
          | inl p2 =>
            rw [Sum.inr_le_inr_iff] at le
            cases le
          | inr p2 =>
            simp
            rw [Sum.inr_le_inr_iff] at le
            replace le := Sum.Lex.inr_le_inr_iff.1 le
            apply Sum.Lex.inr_le_inr_iff.2 le
  constructor
  · intro p
    cases p with 
    | inl p => simp
    | inr p => cases p with 
      | inl p => simp
      | inr p => simp
  · intro p1 p2 eq
    cases p1 with
    | inl p1 => cases p2 with
      | inl p2 => 
        simp at *
        apply Sum.inl_injective at eq
        apply Sum.inl_injective at eq
        congr
      | inr p2 => cases p2 with
        | inl p2 => simp at *; cases eq
        | inr p2 => simp at *
    | inr p1 => cases p2 with
      | inl p2 => cases p1 with
        | inl p1 => simp at *; cases eq
        | inr p1 => simp at *
      | inr p2 => cases p1 with
        | inl p1 => cases p2 with
          | inl p2 =>
            simp at *
            cases eq; rfl
          | inr p2 => simp at *
        | inr p1 => cases p2 with
          | inl p2 => simp at *
          | inr p2 =>
            simp at *
            cases eq; rfl

lemma at_and_seq : (t.and u).seq w ≤ t.and (u.seq w) := by 
  intro H Hmem
  rcases Hmem with ⟨TU, W, ⟨T, U, hT, hU, hTU⟩, hW, hTUW⟩
  use (T.merge (U.earlier W))
  · simp [(· ⋈ ·), (· ↝ ·)]
    constructor
    · use T, hT, U ▷ W
      constructor
      · use U, hU, W, hW
      · rfl
    · rw [hTUW, hTU]
      refine Quotient.inductionOn₃ T U W fun
      | t, u, w => by exact and_seq_le

end and_seq 

section seq_and 

@[simp]
def seq_and_fun {U V W : LPO lab} (x : (V.merge (U.earlier W)).t) :
(U.earlier (V.merge W)).t := 
match x with 
| (.inl v) => .inr (.inl v)
| (.inr (.inl u)) => .inl u 
| (.inr (.inr w)) => .inr (.inr w)

lemma seq_and_le {U V W : LPO lab} :
V.merge (U.earlier W) ≤ U.earlier (V.merge W) := by
  use seq_and_fun
  constructor
  · intro p1 p2 le
    cases p1 with
    | inl p1 => cases p2 with
      | inl p2 => 
        simp
        apply Sum.Lex.inr_mono
        apply Sum.inl_mono
        exact Sum.inl_le_inl_iff.mp le
      | inr p2 => cases le
    | inr p1 => cases p2 with
      | inl p2 => cases le
      | inr p2 => cases p2 with
        | inl p2 => cases p1 with
          | inl p1 => 
            simp
            rw [Sum.inr_le_inr_iff] at le
            replace le := Sum.Lex.inl_le_inl_iff.1 le
            apply Sum.Lex.inl_le_inl_iff.2 le
          | inr p1 =>
            rw [Sum.inr_le_inr_iff] at le
            cases le
        | inr p2 => cases p1 with
          | inl p1 =>
            simp
            apply Sum.Lex.inl_le_inr
          | inr p1 =>
            simp
            rw [Sum.inr_le_inr_iff] at le
            replace le := Sum.Lex.inr_le_inr_iff.1 le
            apply Sum.Lex.inr_le_inr_iff.2
            exact Sum.inr_le_inr_iff.2 le
  constructor
  · intro p
    cases p with 
    | inl p => simp
    | inr p => cases p with
      | inl p => simp
      | inr p => simp
  · intro p1 p2 eq
    cases p1 with
    | inl p1 => cases p2 with
      | inl p2 =>
        simp at *
        cases eq; rfl
      | inr p2 => cases p2 with
        | inl p2 => simp at *
        | inr p2 => simp at *; cases eq
    | inr p1 => cases p1 with
      | inl p1 => cases p2 with
        | inl p2 => simp at *
        | inr p2 => cases p2 with
          | inl p2 => simp at *; cases eq; rfl
          | inr p2 => simp at *
      | inr p1 => cases p2 with
        | inl p2 => simp at *; cases eq
        | inr p2 => cases p2 with 
          | inl p2 => simp at *
          | inr p2 => simp at *; cases eq; rfl 

end seq_and 

section seq_le_and

@[simp]
def seq_le_and_fun {T U : LPO lab} (x : (T.merge U).t) :
(T.earlier U).t :=
match x with 
| (.inl t) => .inl t 
| (.inr u) => .inr u 

lemma seq_le_and_le {T U : LPO lab} : T.merge U ≤ T.earlier U := by 
  use seq_le_and_fun
  constructor
  · intro p1 p2 le
    cases p1 <;> cases p2
    · simp; apply Sum.Lex.inl_mono; exact Sum.inl_le_inl_iff.mp le 
    · cases le
    · cases le
    · simp; apply Sum.Lex.inr_mono; exact Sum.inr_le_inr_iff.mp le
  constructor
  · intro p; cases p; simp; simp
  · intro p1 p2 eq
    cases p1 <;> cases p2
    · simp at *; cases eq; rfl
    · simp at *
    · simp at *
    · simp at *; cases eq; rfl 

lemma at_seq_le_and (t u : AttackTree lab) : t.seq u ≤ t.and u := by 
  rw [Supports.AT.le_def]
  intro H Hmem
  rcases Hmem with ⟨a, b, ha, hb, hab⟩
  use a ⊎ b
  constructor
  · simp [(· ⋈ ·)]
    use a, ha, b, hb
  · rw [hab] 
    exact Quotient.inductionOn₂ a b (λ _ _ => seq_le_and_le)

end seq_le_and 

end Supports 
end supports

section covers
namespace Covers 

--local attribute [reducible] Covers.AttCov Covers.cop_cov
local instance : Preorder (AttackTree lab) := AT.covers_preorder lab 

variable {lab : Type} {t u v w : Covers.AttCov lab}

section seq_and_seq

@[simp]
def seq_and_seq_fun {T U V W : LPO lab} 
(x : ((T.earlier V).merge (U.earlier W)).t) :
((T.merge U).earlier (V.merge W)).t :=
match x with 
| (.inl (.inl t)) => (.inl (.inl t))
| (.inl (.inr v)) => (.inr (.inl v))
| (.inr (.inl u)) => (.inl (.inr u))
| (.inr (.inr w)) => (.inr (.inr w))


lemma seq_and_seq_le {T U V W : LPO lab} : 
((T.earlier V).merge (U.earlier W)) ≤ ((T.merge U).earlier (V.merge W)) := by
  use seq_and_seq_fun
  constructor
  · intro p1 p2 le
    cases p1 with
    | inl p1 => cases p1 with
      | inl p1 => cases p2 with
        | inl p2 => cases p2 with
          | inl p2 => 
            simp
            apply Sum.Lex.inl_mono;
            apply Sum.inl_mono 
            rw [Sum.inl_le_inl_iff] at le
            exact Sum.Lex.inl_le_inl_iff.mp le
          | inr p2 => simp; apply Sum.Lex.inl_le_inr
        | inr p2 => cases le
      | inr p1 => cases p2 with
        | inl p2 => cases p2 with
          | inl p2 => rw [Sum.inl_le_inl_iff] at le; cases le
          | inr p2 =>
            simp
            apply Sum.Lex.inr_mono
            apply Sum.inl_mono 
            rw [Sum.inl_le_inl_iff] at le
            exact Sum.Lex.inr_le_inr_iff.mp le
        | inr p2 => cases le
    | inr p1 => cases p1 with
      | inl p1 => cases p2 with
        | inl p2 => cases le
        | inr p2 => cases p2 with
          | inl p2 =>
            simp
            apply Sum.Lex.inl_mono
            apply Sum.inr_mono 
            rw [Sum.inr_le_inr_iff] at le
            exact Sum.Lex.inl_le_inl_iff.mp le
          | inr p2 => simp; apply Sum.Lex.inl_le_inr
      | inr p1 => cases p2 with 
        | inl p2 => cases le
        | inr p2 => cases p2 with
          | inl p2 => rw [Sum.inr_le_inr_iff] at le; cases le
          | inr p2 => 
            simp
            apply Sum.Lex.inr_mono
            apply Sum.inr_mono
            rw [Sum.inr_le_inr_iff] at le
            exact Sum.Lex.inr_le_inr_iff.mp le
  constructor 
  · intro p
    cases p with 
    | inl p => cases p; simp; simp
    | inr p => cases p; simp; simp
  · intro p1 p2 eq
    cases p1 with 
    | inl p1 => cases p1 with
      | inl p1 => cases p2 with
        | inl p2 => cases p2 with
          | inl p2 => simp at *; cases eq; rfl
          | inr p2 => simp at *
        | inr p2 => cases p2 with 
          | inl p2 => simp at *; cases eq
          | inr p2 => simp at *
      | inr p1 => cases p2 with 
        | inl p2 => cases p2 with
          | inl p2 => simp at *
          | inr p2 => simp at *; cases eq; rfl
        | inr p2 => cases p2 with 
          | inl p2 => simp at *
          | inr p2 => simp at *; cases eq
    | inr p1 => cases p1 with 
      | inl p1 => cases p2 with 
        | inl p2 => cases p2 with
          | inl p2 => simp at *; cases eq
          | inr p2 => simp at *
        | inr p2 => cases p2 with 
          | inl p2 => simp at *; cases eq; rfl
          | inr p2 => simp at *
      | inr p1 => cases p2 with
        | inl p2 => cases p2 with
          | inl p2 => simp at *
          | inr p2 => simp at *; cases eq
        | inr p2 => cases p2 with
          | inl p2 => simp at *
          | inr p2 => simp at *; cases eq; rfl

lemma at_seq_and_seq {t u v w : AttackTree lab} : 
((t.seq v).and (u.seq w)) ≤ ((t.and u).seq (v.and w)) := by
  rw [Covers.AT.le_def]
  rintro H ⟨TV, UW, ⟨T, V, hT, hV, hTV⟩, ⟨U, W, hU, hW, hUW⟩, hTVUW⟩
  use ((T ⊎ U) ▷ (V ⊎ W))
  constructor
  · simp [(· ⋈ ·), (· ↝ ·)]
    use T ⊎ U; 
    constructor
    · use T, hT, U, hU
    · use V ⊎ W
      constructor
      · use V, hV, W, hW
      · rfl
  · rw [hTVUW, hTV, hUW]
    refine Quotient.inductionOn W fun 
    | _ => by
      refine Quotient.inductionOn₃ T V U fun
      | t, v, u => by 
        exact seq_and_seq_le

end seq_and_seq

section and_seq 

@[simp]
def and_seq_fun {T U W : LPO lab} (x : (T.merge (U.earlier W)).t) :
((T.merge U).earlier W).t :=
match x with 
| (.inl t) => .inl (.inl t)
| (.inr (.inl u)) => .inl (.inr u)
| (.inr (.inr w)) => .inr w 
 

lemma and_seq_le {T U W : LPO lab} : 
T.merge (U.earlier W) ≤ ((T.merge U).earlier W) := by 
  use and_seq_fun
  constructor
  · intro p1 p2 le
    cases p1 with 
    | inl p1 => cases p2 with
      | inl p2 => 
        simp
        apply Sum.Lex.inl_mono 
        apply Sum.inl_mono 
        exact Sum.inl_le_inl_iff.mp le
      | inr p2 => cases le
    | inr p1 => cases p1 with 
      | inl p1 => cases p2 with
        | inl p2 => cases le
        | inr p2 => cases p2 with
          | inl p2 => 
            simp
            apply Sum.Lex.inl_mono 
            apply Sum.inr_mono
            rw [Sum.inr_le_inr_iff] at le
            exact Sum.Lex.inl_le_inl_iff.mp le
          | inr p2 => simp; apply Sum.Lex.inl_le_inr
      | inr p1 => cases p2 with
        | inl p2 => cases le
        | inr p2 => cases p2 with
          | inl p2 => 
            rw [Sum.inr_le_inr_iff] at le
            cases le
          | inr p2 =>
            simp
            apply Sum.Lex.inr_mono 
            rw [Sum.inr_le_inr_iff] at le
            exact Sum.Lex.inr_le_inr_iff.mp le
  constructor
  · intro p; rcases p with p | p; simp; cases p; simp; simp
  · intro p1 p2 eq
    cases p1 with
    | inl p1 => cases p2 with 
      | inl p2 => simp at *; cases eq; rfl
      | inr p2 => cases p2 with
        | inl p2 => simp at *; cases eq
        | inr p2 => simp at *
    | inr p1 => cases p1 with
      | inl p1 => cases p2 with 
        | inl p2 => simp at *; cases eq
        | inr p2 => cases p2 with 
          | inl p2 => simp at *; cases eq; rfl
          | inr p2 => simp at *
      | inr p1 => cases p2 with
        | inl p2 => simp at *
        | inr p2 => cases p2 with
          | inl p2 => simp at *
          | inr p2 => simp at *; cases eq; rfl

lemma at_and_seq {t u w : AttackTree lab} : 
t.and (u.seq w) ≤ ((t.and u).seq w) := by 
  rw [Covers.AT.le_def]
  rintro H ⟨T, UW, hT, ⟨U, W, hU, hW, hUW⟩, hTUW⟩
  use ((T ⊎ U) ▷ W)
  constructor
  · simp [(· ⋈ ·), (· ↝ ·)]
    use T ⊎ U
    constructor
    · use T, hT, U, hU
    · use W, hW
  · rw [hTUW, hUW]
    refine Quotient.inductionOn₃ T U W fun
    | t, u, w => by 
      exact and_seq_le

end and_seq

section seq_and

@[simp]
def seq_and_fun {V U W : LPO lab} (x : (V.merge (U.earlier W)).t) :
(U.earlier (V.merge W)).t := 
match x with 
| (.inl v) => (.inr (.inl v))
| (.inr (.inl u)) => .inl u 
| (.inr (.inr w)) => (.inr (.inr w))

lemma seq_and_le {V U W : LPO lab} :
V.merge (U.earlier W) ≤ U.earlier (V.merge W) := by 
  use seq_and_fun
  constructor
  · intro p1 p2 le
    cases p1 with
    | inl p1 => cases p2 with
      | inl p2 =>
        simp
        apply Sum.Lex.inr_mono 
        apply Sum.inl_mono 
        exact Sum.inl_le_inl_iff.mp le
      | inr p2 => cases le
    | inr p1 => cases p1 with
      | inl p1 => cases p2 with 
        | inl p2 => cases le
        | inr p2 => cases p2 with 
          | inl p2 =>
            simp
            apply Sum.Lex.inl_mono 
            rw [Sum.inr_le_inr_iff] at le
            exact Sum.Lex.inl_le_inl_iff.mp le
          | inr p2 => simp; apply Sum.Lex.inl_le_inr
      | inr p1 => cases p2 with
        | inl p2 => cases le
        | inr p2 => cases p2 with
          | inl p2 => 
            rw [Sum.inr_le_inr_iff] at le
            cases le
          | inr p2 =>
            simp
            apply Sum.Lex.inr_mono
            apply Sum.inr_mono
            rw [Sum.inr_le_inr_iff] at le
            exact Sum.Lex.inr_le_inr_iff.mp le
  constructor
  · intro p; rcases p with p | p; simp; cases p; simp; simp
  · intro p1 p2 eq
    cases p1 with
    | inl p1 => cases p2 with
      | inl p2 => simp at *; cases eq; rfl
      | inr p2 => cases p2 with
        | inl p2 => simp at *
        | inr p2 => simp at *; cases eq
    | inr p1 => cases p1 with
      | inl p1 => cases p2 with
        | inl p2 => simp at *
        | inr p2 => cases p2 with
          | inl p2 => simp at *; cases eq; rfl
          | inr p2 => simp at *
      | inr p1 => cases p2 with
        | inl p2 => simp at *; cases eq
        | inr p2 => cases p2 with
          | inl p2 => simp at *
          | inr p2 => simp at *; cases eq; rfl

lemma at_seq_and {v u w : AttackTree lab} :
v.and (u.seq w) ≤ u.seq (v.and w) := by 
  rw [Covers.AT.le_def]
  rintro H ⟨V, UW, hV, ⟨U, W, hU, hW, hUW⟩, hVUW⟩
  use U ▷ (V ⊎ W)
  constructor
  · simp [(· ⋈ ·), (· ↝ ·)]
    use U, hU, V ⊎ W
    constructor
    · use V, hV, W, hW
    · rfl
  · rw [hVUW, hUW]
    refine Quotient.inductionOn₃ V U W fun
    | v, u, w => by 
      exact seq_and_le

end seq_and

section and_le_seq

@[simp]
def and_le_seq_fun {T U : LPO lab} (x : (T.merge U).t) :
(T.earlier U).t :=
match x with 
| (.inl t) => .inl t 
| (.inr u) => .inr u 

lemma and_le_seq_le {T U : LPO lab} :
T.merge U ≤ T.earlier U := by 
  use and_le_seq_fun
  constructor
  · intro p1 p2 le
    cases p1 <;> cases p2
    · simp 
      rw [Sum.inl_le_inl_iff] at le
      exact Sum.Lex.inl_le_inl_iff.2 le
    · cases le
    · cases le
    · simp
      rw [Sum.inr_le_inr_iff] at le
      exact Sum.Lex.inr_le_inr_iff.2 le
  constructor
  · intro p; cases p; simp; simp
  · intro p1 p2 eq
    cases p1 <;> cases p2
    · simp at *; cases eq; rfl
    · simp at *
    · simp at *
    · simp at *; cases eq; rfl

lemma at_and_le_seq {t u : AttackTree lab} :
t.and u ≤ t.seq u := by 
  rw [Covers.AT.le_def]
  rintro H ⟨T, U, hT, hU, hTU⟩
  use T ▷ U
  constructor
  · use T, U, hT, hU
  · rw [hTU]
    refine Quotient.inductionOn₂ T U fun
    | t, u => by exact and_le_seq_le

end and_le_seq

end Covers
end covers 
