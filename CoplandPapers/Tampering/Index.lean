import Mathlib

set_option autoImplicit false

open scoped Classical 
open List

section IndexDefs 

variable {A : Type} (l : List A)

/--
  The type of valid indices into `l` can be thought of as 
  a `n : ℕ` together with evidence `hn` that `n < length l`.
-/
def Idx := { n : ℕ // n < length l }

instance {l : List A} {a : A} : Zero (Idx (a::l)) where 
  zero := ⟨0, by simp⟩

--#check Idx 

/- Omit defs for projections since they are simple in Lean. -/

lemma idx_nat_lt_length (i : Idx l) : i.1 < length l := i.2 

    
@[ext]
lemma idx_ext {l : List A} {i j : Idx l} (eq : i.1 = j.1) : i = j := by 
  cases i; cases j; subst eq; rfl 

lemma idx_eq_iff (i j : Idx l) : i = j ↔ i.1 = j.1 := by 
  constructor <;> intro eq 
  · cases eq; rfl 
  · ext; assumption
    
def to_idx {l : List A} {n : ℕ} (hn : n < length l) : Idx l := ⟨n, hn⟩

end IndexDefs

section IndexBasics 

variable {A : Type} {l : List A}

lemma idx_single (a : A) (i : Idx [a]) : i.1 = 0 := by 
  obtain ⟨n, hn⟩ := i 
  simp at hn ⊢
  exact hn

lemma app_idx_rht_bnd (l1 l2 : List A) (i : Idx (l1 ++ l2))
    (leq : length l1 ≤ i.1) : i.1 - length l1 < length l2 := by 
  exact get_append_right_aux leq i.2

lemma app3_idx_nat_range (l1 l2 l3 : List A) (i : Idx (l1 ++ l2 ++ l3)) :
    i.1 < length l1 ∨ 
    length l1 ≤ i.1 ∧ i.1 < (length l1 + length l2) ∨
    length l1 + length l2 ≤ i.1 ∧ i.1 < length l1 + length l2 + length l3 := by
  obtain ⟨n, hn⟩ := i
  simp
  rw [length_append, length_append] at hn
  omega 
  
lemma app4_idx_nat_range (l1 l2 l3 l4 : List A) 
    (i : Idx (l1 ++ l2 ++ l3 ++ l4)) :
    i.1 < length l1 ∨ 
    length l1 ≤ i.1 ∧ i.1 < (length l1 + length l2) ∨
    length l1 + length l2 ≤ i.1 ∧ i.1 < length l1 + length l2 + length l3 ∨
    length l1 + length l2 + length l3 ≤ i.1 ∧ i.1 ≤ length l1 + length l2 + length l3 + length l4 := by 
  obtain ⟨n, hn⟩ := i
  rw [length_append, length_append, length_append] at hn 
  simp 
  omega 
  
end IndexBasics 

section NthSafe 

section NthSafeDef

def nth_safe {A : Type} (l : List A) (i : Idx l) : A := by 
  obtain ⟨n, hn⟩ := i 
  cases l with
  | nil => simp at hn 
  | cons a l' => 
    cases n with
    | zero => use a 
    | succ k => 
      simp at hn 
      rw [Nat.succ_lt_succ_iff] at hn
      use nth_safe l' ⟨k, hn⟩

end NthSafeDef 

lemma nth_safe_evi_indep {A : Type} (l : List A) (n : ℕ) 
    (hn hn' : n < length l) : 
    nth_safe l ⟨n, hn⟩ = nth_safe l ⟨n, hn'⟩ := rfl

lemma nth_safe_nat_eq {A : Type} (l : List A) (i j : Idx l)
    (eq : i.1 = j.1) : nth_safe l i = nth_safe l j := by 
  apply idx_ext at eq 
  subst eq 
  rfl 

@[simp]  
lemma nth_safe_sngl {A : Type} (a : A) (i : Idx [a]) : 
    nth_safe [a] i = a := by 
  have h := idx_single _ i
  obtain ⟨n, hn⟩ := i 
  subst h 
  simp [nth_safe]
  
lemma nth_safe_fst {A : Type} (l : List A) (a : A) (i : Idx (a::l)) 
    (eq : i.1 = 0) : nth_safe (a::l) i = a := by 
  obtain ⟨n, hn⟩ := i 
  simp_all
  substs
  dsimp [nth_safe]

lemma nth_safe_cons {A : Type} (l : List A) (a : A) n hsn hn : 
    nth_safe (a::l) ⟨n + 1, hsn⟩ = nth_safe l ⟨n, hn⟩ := by 
  revert a n
  cases l with
  | nil => intro a n hsn hn; simp at hn 
  | cons a' l' => 
    intro a n hsn _  
    dsimp [nth_safe]

lemma nth_safe_app_lft {A : Type} (l1 l2 : List A) (i : Idx (l1 ++ l2)) 
    (hn' : i.1 < length l1) :
    nth_safe (l1 ++ l2) i = nth_safe l1 (to_idx hn') := by 
  obtain ⟨n, hn⟩ := i 
  revert n l2 
  induction l1 with 
  | nil => simp
  | cons a l1' ih => 
    intro l2 n hn hn' 
    cases n with 
    | zero => rfl
    | succ k => 
      dsimp [to_idx, nth_safe]
      apply ih 

lemma nth_safe_app_rht {A : Type} (l1 l2 : List A) (i : Idx (l1 ++ l2)) 
    (le : length l1 ≤ i.1) (hn' : i.1 - length l1 < length l2) :
    nth_safe (l1 ++ l2) i = nth_safe l2 (to_idx hn') := by
  obtain ⟨n, hn⟩ := i 
  revert n l2 
  induction l1 with
  | nil => 
    intro l2 n hn _ _ 
    rfl
  | cons a l1' ih => 
    intro l2 n hn le hn' 
    cases n with 
    | zero => simp at le      
    | succ k => 
      simp only [length_cons, Nat.succ_sub_succ_eq_sub]
      apply ih
      simp_all 
      linarith
    
lemma nth_safe_app {A : Type} (l1 l2 : List A) (i : Idx (l1 ++ l2)) : 
    (i.1 < length l1 ∧ 
     ∀ (hn' : i.1 < length l1), 
     nth_safe (l1 ++ l2) i = nth_safe l1 (to_idx hn')) ∨ 
    (length l1 ≤ i.1 ∧ 
     ∀ (hn' : i.1 - length l1 < length l2), 
     nth_safe (l1 ++ l2) i = nth_safe l2 (to_idx hn')) := by 
  by_cases lt : i.1 < length l1 
  · left 
    use lt 
    intro hn'
    exact nth_safe_app_lft l1 l2 i hn'
  · right 
    apply Nat.ge_of_not_lt at lt
    use lt 
    intro hn'
    exact nth_safe_app_rht l1 l2 i lt hn'
  
lemma nth_safe_map {A B : Type} (l : List A) (f : A → B) (i : Idx l) 
    (i' : Idx (map f l)) (eq : i'.1 = i.1) : 
    nth_safe (map f l) i' = f (nth_safe l i) := by 
  revert i i' 
  induction l with 
  | nil => 
    rintro ⟨n, hn⟩
    cases hn    
  | cons a l ih => 
    intro i i' eq 
    cases l with 
    | nil => simp
    | cons a' l' => 
      simp 
      obtain ⟨n', hn'⟩ := i'  
      obtain ⟨n, hn⟩ := i 
      simp_all      
      cases n with 
      | zero => 
        simp_all
        dsimp [nth_safe]        
      | succ k => 
        rw [nth_safe_cons, nth_safe_cons]
        apply ih 
        simp 
        exact nth_safe.proof_3 a (a' :: l') k hn
        simp at hn' 
        rw [eq, Nat.succ_lt_succ_iff] at hn' 
        simp 
        exact hn' 
        


end NthSafe
