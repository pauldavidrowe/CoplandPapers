--import data.real.basic
import CoplandPapers.OnOrderings.Supports 
import CoplandPapers.OnOrderings.Covers 

/-
  This file introduces the machinery to define attribute domains. 

  An attribute domain is essentially a function parameterized by
  * a set of operators
  * an ordered domain of interpretation
  * a base function from atomic elements to the domain of interpretation

  The function then describes how to the extend the base function
  to elements composed by the operators. 

  Our definitions are not completely general. We rely on knowing 
  the number of each operator of each arity, and a single family 
  of attribute domains is defined for each such choice. Since 
  we know that information for both attack trees and Copland 
  phrases, we can define a family of attribute domains for both 
  attack trees and Copland phrases. 

  We then define co-variant and contra-variant soundness of 
  attribute domains. We finally set up the machinery necessary
  to prove that if an attack tree is sound then so is its 
  "corresponding" Copland phrase. We then show such reductions
  for the four attribute domains considered in the paper 
  on specializing attack trees. 
-/

variable {p : Place} {Lab : Type}

open AttackTree Copland 

-- Type synonym incorporating p 
def Copland_p (_ : Place) := Copland 

-- The family of attribute domains for attack trees 
@[simp]
def att_ad {Vals : Type} (l2 : Vector (Vals → Vals → Vals) 3)
(V : AttackTree Lab → Vals) : AttackTree Lab → Vals 
| (.atm a) => V (.atm a)
| (.or t1 t2) => (Vector.get l2 0) (att_ad l2 V t1) (att_ad l2 V t2)
| (.and t1 t2) => (Vector.get l2 1) (att_ad l2 V t1) (att_ad l2 V t2)
| (.seq t1 t2) => (Vector.get l2 2) (att_ad l2 V t1) (att_ad l2 V t2)

-- The family of attribute domains for Copland phrases 
@[simp]
def cop_ad {p} {Vals : Type} (l1 : Vals → Vals)   
(l2 : Vector (Vals → Vals → Vals) 3) (V : Copland_p p → Vals) : Copland_p p → Vals
| (.atom a) => V (atom a)
| (.bpar _ c1 c2) => (Vector.get l2 0) (cop_ad l1 l2 V c1) (cop_ad l1 l2 V c2)
| (.lseq c1 c2) => (Vector.get l2 1) (cop_ad l1 l2 V c1) (cop_ad l1 l2 V c2)
| (.bseq _ c1 c2) => (Vector.get l2 2) (cop_ad l1 l2 V c1) (cop_ad l1 l2 V c2)
| (.att _ c1) => l1 (cop_ad l1 l2 V c1)

section soundness

-- Definition of co-variant soundness
def co_sound {Vals Terms : Type} [Preorder Vals] [Preorder Terms] 
(ad : (Terms → Vals) → (Terms → Vals)) :=
∀ t1 t2 (V : Terms → Vals), t1 ≤ t2 → ad V t1 ≤ ad V t2

-- Definition of contra-variant soundness
def contra_sound {Vals Terms : Type} [Preorder Vals] [Preorder Terms] 
(ad : (Terms → Vals) → (Terms → Vals)) :=
∀ t1 t2 (V : Terms → Vals), t1 ≤ t2 → ad V t2 ≤ ad V t1

-- Soundness holds if either type of soundness holds 
def sound {Vals Terms : Type} [Preorder Vals] [Preorder Terms] 
(ad : (Terms → Vals) → (Terms → Vals)) :=
co_sound ad ∨ contra_sound ad 

end soundness 

/-
  Given a Copland phrase, there is a "corresponding" attack tree. 
  Linear and branching sequentials turn into sequentials. Branching
  parallels turn into conjunctions. Remote requests get stripped off
  with no counterpart. 
-/
@[simp]
def transfer : Copland → AttackTree Label  
| (.atom a) => (atm (asp_label a))
| (.bpar _ c1 c2) => (and (transfer c1) (transfer c2))
| (.bseq _ c1 c2) => (seq (transfer c1) (transfer c2))
| (.lseq c1 c2) => (seq (transfer c1) (transfer c2))
| (.att _ c1) => transfer c1

-- The semantics of a Copland atom and its corresponding attack tree
-- are exactly equal. 
lemma transfer_eq {a : ASP} :
copland_base_sem p (atom a) = BS (transfer (atom a)) := by simp 

-- For a Copland phrase c, anything in the base semantics of its 
-- corresponding attack tree is ≤ somthing in the semantics of the 
-- Copland phrase itself. 
lemma transfer_le (p : Place) {c : Copland} :
∀ {q : QLPO Label}, q ∈ BS (transfer c) → q ≤ ⟦(cop_sem p c : LPO Label)⟧ := by 
  revert p
  induction' c <;> intro p q
  case atom a
  · simp; exact le_of_eq
  case lseq c1 c2 IH1 IH2
  · intro mem
    rcases mem with ⟨q1, q2, mem1, mem2, eq⟩; subst eq
    revert mem1 mem2
    refine Quotient.inductionOn₂ q1 q2 fun
    | l1, l2 => by
      clear q1 q2
      intros mem1 mem2
      specialize @IH1 p _ mem1
      specialize @IH2 p _ mem2
      obtain ⟨f, hf⟩ := IH1; obtain ⟨g, hg⟩ := IH2
      simp
      set fg : (l1.earlier l2).t → (LPO.earlier (cop_sem p c1) (cop_sem p c2)).t :=
      λ x => by
        rcases x with x | x; exact .inl (f x); exact .inr (g x)
        with hfg
      use fg
      constructor
      · intro p1 p2 le; rw [hfg]
        cases p1 <;> cases p2
        · simp
          replace le := Sum.Lex.inl_le_inl_iff.1 le
          apply Sum.Lex.inl_le_inl_iff.2; exact hf.1 le
        · simp
          apply Sum.Lex.inl_le_inr
        · simp; cases le
        · simp
          replace le := Sum.Lex.inr_le_inr_iff.1 le
          apply Sum.Lex.inr_le_inr_iff.2
          exact hg.1 le
      constructor 
      · intro p1; cases p1 <;> simp; 
        · rw [hf.2.1]; simp [fg]
        · rw [hg.2.1]; simp [fg]
      · intro p1 p2 eq
        cases p1 <;> cases p2
        · simp [hfg] at eq
          rw [Sum.inl.injEq] at eq
          replace eq := hf.2.2 eq
          rw [eq]
        · simp [hfg] at eq
        · simp [hfg] at eq
        · simp [hfg] at eq;
          rw [Sum.inr.injEq] at eq
          replace eq := hg.2.2 eq
          rw [eq]
  case bseq s c1 c2 IH1 IH2
  · intro mem
    rcases mem with ⟨q1, q2, mem1, mem2, eq⟩; subst eq
    revert mem1 mem2
    refine Quotient.inductionOn₂ q1 q2 fun
    | l1, l2 => by
      clear q1 q2
      intros mem1 mem2
      specialize @IH1 p _ mem1; obtain ⟨f, hf⟩ := IH1
      specialize @IH2 p _ mem2; obtain ⟨g, hg⟩ := IH2 
      simp
      set fg : (l1.earlier l2).t → (LPO.earlier 
      (evsys_of_label Label.split) 
      ((LPO.earlier (cop_sem p c1) (cop_sem p c2)).earlier 
        (evsys_of_label Label.joins))).t :=
      λ x => by
        rcases x with x | x; exact (.inr (.inl (.inl (f x))))
        exact (.inr (.inl (.inr (g x))))
        with hfg
      use fg --rw hfg,
      constructor
      · intros p1 p2 le; rw [hfg]
        cases p1 <;> cases p2 <;> simp
        · cases le
          apply Sum.Lex.inr_le_inr_iff.2
          apply Sum.Lex.inl_le_inl_iff.2
          apply Sum.Lex.inl_le_inl_iff.2
          apply hf.1; assumption
        · apply Sum.Lex.inr_le_inr_iff.2
          apply Sum.Lex.inl_le_inl_iff.2
          apply Sum.Lex.inl_le_inr
        · cases le
        · cases le
          apply Sum.Lex.inr_le_inr_iff.2
          apply Sum.Lex.inl_le_inl_iff.2
          apply Sum.Lex.inr_le_inr_iff.2
          apply hg.1; assumption
      constructor 
      · intro p1; rw [hfg]; cases p1 <;> simp
        rw [hf.2.1]; rw [hg.2.1]
      · intro p1 p2 eq 
        cases p1 <;> cases p2 <;> simp [hfg] at eq
        · rw [Sum.inr.injEq] at eq
          rw [Sum.inl.injEq] at eq
          rw [Sum.inl.injEq] at eq
          replace eq := hf.2.2 eq
          rw [eq]
        · rw [Sum.inr.injEq] at eq
          rw [Sum.inl.injEq] at eq
          cases eq
        · rw [Sum.inr.injEq] at eq
          rw [Sum.inl.injEq] at eq
          cases eq
        · rw [Sum.inr.injEq] at eq
          rw [Sum.inl.injEq] at eq
          rw [Sum.inr.injEq] at eq
          replace eq := hg.2.2 eq 
          rw [eq]
  case bpar s c1 c2 IH1 IH2
  · intro mem
    rcases mem with ⟨q1, q2, mem1, mem2, eq⟩; subst eq
    revert mem1 mem2
    refine Quotient.inductionOn₂ q1 q2 fun
    | l1, l2 => by
      clear q1 q2
      intros mem1 mem2
      specialize @IH1 p _ mem1; obtain ⟨f, hf⟩ := IH1
      specialize @IH2 p _ mem2; obtain ⟨g, hg⟩ := IH2
      simp
      set fg : (l1.merge l2).t → (LPO.earlier 
        (evsys_of_label Label.split) 
        ((LPO.merge (cop_sem p c1) (cop_sem p c2)).earlier 
          (evsys_of_label Label.joins))).t :=
      λ x => by 
        rcases x with x | x; exact (.inr (.inl (.inl (f x))))
        exact (.inr (.inl (.inr (g x))))
        with hfg
      use fg
      constructor
      · intro p1 p2 le
        cases p1 <;> cases p2 <;> rw [hfg] <;> simp
        · rw [Sum.inl_le_inl_iff] at le
          apply Sum.Lex.inr_le_inr_iff.2
          apply Sum.Lex.inl_le_inl_iff.2
          rw [Sum.inl_le_inl_iff]
          exact hf.1 le
        · cases le
        · cases le
        · rw [Sum.inr_le_inr_iff] at le
          apply Sum.Lex.inr_le_inr_iff.2
          apply Sum.Lex.inl_le_inl_iff.2
          rw [Sum.inr_le_inr_iff]
          exact hg.1 le
      constructor
      · intro p1; cases p1 <;> rw [hfg] <;> simp
        rw [hf.2.1]; rw [hg.2.1]
      · intro p1 p2 eq
        cases p1 <;> cases p2 <;> rw [hfg] at eq <;> simp at eq
        · rw [Sum.inr.injEq] at eq
          rw [Sum.inl.injEq] at eq
          rw [Sum.inl.injEq] at eq
          replace eq := hf.2.2 eq
          rw [eq]
        · rw [Sum.inr.injEq] at eq
          rw [Sum.inl.injEq] at eq
          cases eq
        · rw [Sum.inr.injEq] at eq
          rw [Sum.inl.injEq] at eq
          cases eq
        · rw [Sum.inr.injEq] at eq
          rw [Sum.inl.injEq] at eq
          rw [Sum.inr.injEq] at eq
          replace eq := hg.2.2 eq
          rw [eq]
  case att r c1 IH1
  · refine Quotient.inductionOn q fun
    | l => by
      clear q
      intro mem; simp at mem
      specialize @IH1 r _ mem
      obtain ⟨f, hf⟩ := IH1
      simp
      set fg : l.t → (LPO.earlier (evsys_of_label (Label.req p r)) 
        (LPO.earlier (cop_sem r c1) 
        (evsys_of_label (Label.req p r)))).t := 
      λ x => (.inr (.inl (f x))) with hfg
      use fg
      constructor
      · intro p1 p2 le; rw [hfg]; simp
        apply Sum.Lex.inr_le_inr_iff.2
        apply Sum.Lex.inl_le_inl_iff.2
        apply hf.1 le
      constructor
      · intro p1; rw [hfg]; simp; rw [hf.2.1]
      · intro p1 p2 eq; simp [hfg] at eq
        rw [Sum.inr.injEq] at eq
        rw [Sum.inl.injEq] at eq
        exact hf.2.2 eq

-- Utility lemma saying that all events in the semantics of
-- an attack tree corresponding to a Copland phrase correspond to ASPs. 
lemma transfer_label (p : Place) (c : Copland) : 
∀ {l1 : LPO Label} (x : l1.t), ⟦l1⟧ ∈ BS (transfer c) → 
IsASPLabel (l1.l x) := by 
  revert p
  induction' c <;> intro p l1 x mem
  case atom a
  · simp at mem
    obtain ⟨⟨e, he⟩, tmp⟩ := mem; clear tmp
    specialize he x; simp at he
    rw [he]; cases a; simp [asp_label] at *
    all_goals simp [asp_label]
  case lseq c1 c2 IH1 IH2
  · simp at mem
    rw [QLPO.mem_seq_comp_iff] at mem
    rcases mem with ⟨la, lb, eq, ha, hb⟩
    change ⟦l1⟧ = ⟦la.earlier lb⟧ at eq
    simp at eq
    rcases eq with ⟨⟨e, he⟩, tmp⟩; clear tmp
    rw [he]
    rcases (e.toEquiv.toFun x) with val | val
    · specialize @IH1 p la val ha
      simp at IH1 ⊢; assumption
    · specialize @IH2 p lb val hb
      simp at IH2 ⊢; assumption
  case bseq s c1 c2 IH1 IH2
  · simp at mem
    rw [QLPO.mem_seq_comp_iff] at mem
    rcases mem with ⟨la, lb, eq, ha, hb⟩
    change ⟦l1⟧ = ⟦la.earlier lb⟧ at eq
    simp at eq
    rcases eq with ⟨⟨e, he⟩, tmp⟩; clear tmp
    rw [he]
    rcases (e.toEquiv.toFun x) with val | val
    · specialize @IH1 p la val ha
      simp at IH1 ⊢; assumption
    · specialize @IH2 p lb val hb
      simp at IH2 ⊢; assumption
  case bpar s c1 c2 IH1 IH2
  · simp at mem
    rw [QLPO.mem_dist_prod_iff] at mem
    rcases mem with ⟨la, lb, eq, ha, hb⟩
    change ⟦l1⟧ = ⟦la.merge lb⟧ at eq
    simp at eq
    rcases eq with ⟨⟨e, he⟩, tmp⟩; clear tmp
    rw [he]
    rcases (e.toEquiv.toFun x) with val | val
    · specialize @IH1 p la val ha
      simp at IH1 ⊢; assumption
    · specialize @IH2 p lb val hb
      simp at IH2 ⊢; assumption
  case att q c1 IH1
  · simp at mem
    exact @IH1 p l1 x mem

section inductive_cases
-- To save on memory usage, we break out the inductive cases 
-- for the main result below into separate lemmas. 

  lemma le_transfer_atom (a : ASP) {p : Place} (l1 : LPO Label)
  (mem : ⟦l1⟧ ∈ BS (transfer (atom a))) :
  ∃ (f : {z // IsASPLabel ((cop_sem p (atom a)).l z)} → l1.t),
  (∀ (z1 z2 : {z // IsASPLabel ((cop_sem p (atom a)).l z)}),
          f z1 ≤ f z2 ↔ z1 ≤ z2) ∧
  (∀ (z1 : {z // IsASPLabel ((cop_sem p (atom a)).l z)}),
          l1.l (f z1) = (cop_sem p (atom a)).l ↑z1) ∧
  ∀ (z1 z2 : {z // IsASPLabel ((cop_sem p (atom a)).l z)}),
          f z1 = f z2 → z1 = z2 := by
    simp at mem
    rcases mem with ⟨⟨e, he⟩, tmp⟩; clear tmp
    
    use λ (_ : { z : (cop_sem p (atom a)).t // 
                 IsASPLabel ((cop_sem p (atom a)).l z) }) => 
        e.invFun Node.mk --, _, _, _⟩
    constructor
    · intro z1 z2
      obtain ⟨z1, h1⟩ := z1; obtain ⟨z2, h2⟩ := z2
      cases z1; cases z2;
      simp at *
    constructor
    · intro _; apply he
    · intro z1 z2 _
      cases' z1 with z1 h1; cases' z2 with z2 h2
      cases z1; cases z2; rfl

  lemma le_transfer_lseq (c1 c2 : Copland) {p : Place} (l1 : LPO Label)
  (IH1 : ∀ {p : Place} (l1 : LPO Label),
            ⟦l1⟧ ∈ BS (transfer c1) →
            (∃ (f : {z // IsASPLabel ((cop_sem p c1).l z)} → l1.t),
                (∀ (z1 z2 : {z // IsASPLabel ((cop_sem p c1).l z)}),
                    f z1 ≤ f z2 ↔ z1 ≤ z2) ∧
                  (∀ (z1 : {z // IsASPLabel ((cop_sem p c1).l z)}),
                      l1.l (f z1) = (cop_sem p c1).l ↑z1) ∧
                    ∀ (z1 z2 : {z // IsASPLabel ((cop_sem p c1).l z)}),
                      f z1 = f z2 → z1 = z2))
  (IH2 : ∀ {p : Place} (l1 : LPO Label),
            ⟦l1⟧ ∈ BS (transfer c2) →
            (∃ (f : {z // IsASPLabel ((cop_sem p c2).l z)} → l1.t),
                (∀ (z1 z2 : {z // IsASPLabel ((cop_sem p c2).l z)}),
                    f z1 ≤ f z2 ↔ z1 ≤ z2) ∧
                  (∀ (z1 : {z // IsASPLabel ((cop_sem p c2).l z)}),
                      l1.l (f z1) = (cop_sem p c2).l ↑z1) ∧
                    ∀ (z1 z2 : {z // IsASPLabel ((cop_sem p c2).l z)}),
                      f z1 = f z2 → z1 = z2))
  (mem : ⟦l1⟧ ∈ BS (transfer (c1.lseq c2))) :
  ∃ (f : {z // IsASPLabel ((cop_sem p (c1.lseq c2)).l z)} → l1.t),
  (∀ (z1 z2 : {z // IsASPLabel ((cop_sem p (c1.lseq c2)).l z)}),
        f z1 ≤ f z2 ↔ z1 ≤ z2) ∧
  (∀ (z1 : {z // IsASPLabel ((cop_sem p (c1.lseq c2)).l z)}),
          l1.l (f z1) = (cop_sem p (c1.lseq c2)).l ↑z1) ∧
  ∀ (z1 z2 : {z // IsASPLabel ((cop_sem p (c1.lseq c2)).l z)}),
          f z1 = f z2 → z1 = z2 := by 
    simp at mem
    rw [QLPO.mem_seq_comp_iff] at mem
    rcases mem with ⟨la, lb, eq, ha, hb⟩
    change ⟦l1⟧ = ⟦la.earlier lb⟧ at eq
    simp at eq
    rcases eq with ⟨⟨e, he⟩, tmp⟩; clear tmp
    specialize @IH1 p la ha
    rcases IH1 with ⟨f, hf1, hf2, hf3⟩
    specialize @IH2 p lb hb
    rcases IH2 with ⟨g, hg1, hg2, hg3⟩
    --refine ⟨_, _, _, _⟩,
    use by
      exact λ x => by
        cases' x with x hx
        rcases x with x | x
        · exact e.invFun (.inl (f ⟨x, hx⟩))
        · exact e.invFun (.inr (g ⟨x, hx⟩))
    constructor
    · intro z1 z2
      obtain ⟨z1, hz1⟩ := z1; obtain ⟨z2, hz2⟩ := z2
      cases z1 with 
      | inl z1 => cases z2 with 
        | inl z2 => 
          simp 
          constructor <;> intro le
          · apply Sum.Lex.inl_mono 
            apply (hf1 ⟨z1, hz1⟩ ⟨z2, hz2⟩).1
            exact Sum.Lex.inl_le_inl_iff.mp le
          · apply Sum.Lex.inl_mono 
            apply Sum.Lex.inl_le_inl_iff.mp at le
            exact (hf1 ⟨z1, hz1⟩ ⟨z2, hz2⟩).2 le
        | inr z2 => 
          simp
          constructor <;> intro _ 
          · apply Sum.Lex.inl_le_inr
          · apply Sum.Lex.inl_le_inr
      | inr z1 => cases z2 with
        | inl z2 => 
          simp
          constructor <;> intro le <;> cases le
        | inr z2 => 
          simp
          constructor <;> intro le
          · apply Sum.Lex.inr_mono
            apply Sum.Lex.inr_le_inr_iff.mp at le
            exact (hg1 ⟨z1, hz1⟩ ⟨z2, hz2⟩).1 le
          · apply Sum.Lex.inr_mono
            apply Sum.Lex.inr_le_inr_iff.mp at le
            exact (hg1 ⟨z1, hz1⟩ ⟨z2, hz2⟩).2 le
    constructor
    · intro z; obtain ⟨z, hz⟩ := z; cases z
      · simp; rw [he]; simp; rw [hf2]
      . simp; rw [he]; simp; rw [hg2]
    · intro z1 z2 zeq
      obtain ⟨z1, hz1⟩ := z1; obtain ⟨z2, hz2⟩ := z2
      cases z1 with 
      | inl z1 => cases z2 with 
        | inl z2 => 
          simp at zeq ⊢
          rw [Sum.inl.injEq] at zeq ⊢
          apply (hf3 ⟨z1, hz1⟩ ⟨z2, hz2⟩) at zeq 
          simp at zeq; exact zeq
        | inr z2 => simp at zeq
      | inr z1 => cases z2 with 
        | inl z2 => simp at zeq
        | inr z2 => 
          simp at zeq ⊢
          rw [Sum.inr.inj_iff] at zeq ⊢
          apply (hg3 ⟨z1, hz1⟩ ⟨z2, hz2⟩) at zeq
          simp at zeq; exact zeq 
          

  lemma le_transfer_bseq (s : Split) (c1 c2 : Copland) {p : Place} (l1 : LPO Label)
  (IH1 : ∀ {p : Place} (l1 : LPO Label),
            ⟦l1⟧ ∈ BS (transfer c1) →
            (∃ (f : {z // IsASPLabel ((cop_sem p c1).l z)} → l1.t),
                (∀ (z1 z2 : {z // IsASPLabel ((cop_sem p c1).l z)}),
                    f z1 ≤ f z2 ↔ z1 ≤ z2) ∧
                  (∀ (z1 : {z // IsASPLabel ((cop_sem p c1).l z)}),
                      l1.l (f z1) = (cop_sem p c1).l ↑z1) ∧
                    ∀ (z1 z2 : {z // IsASPLabel ((cop_sem p c1).l z)}),
                      f z1 = f z2 → z1 = z2))
  (IH2 : ∀ {p : Place} (l1 : LPO Label),
            ⟦l1⟧ ∈ BS (transfer c2) →
            (∃ (f : {z // IsASPLabel ((cop_sem p c2).l z)} → l1.t),
                (∀ (z1 z2 : {z // IsASPLabel ((cop_sem p c2).l z)}),
                    f z1 ≤ f z2 ↔ z1 ≤ z2) ∧
                  (∀ (z1 : {z // IsASPLabel ((cop_sem p c2).l z)}),
                      l1.l (f z1) = (cop_sem p c2).l ↑z1) ∧
                    ∀ (z1 z2 : {z // IsASPLabel ((cop_sem p c2).l z)}),
                      f z1 = f z2 → z1 = z2))
  (mem : ⟦l1⟧ ∈ BS (transfer (bseq s c1 c2))) :
  ∃ (f : {z // IsASPLabel ((cop_sem p (bseq s c1 c2)).l z)} → l1.t),
  (∀ (z1 z2 : {z // IsASPLabel ((cop_sem p (bseq s c1 c2)).l z)}),
          f z1 ≤ f z2 ↔ z1 ≤ z2) ∧
  (∀ (z1 : {z // IsASPLabel ((cop_sem p (bseq s c1 c2)).l z)}),
            l1.l (f z1) = (cop_sem p (bseq s c1 c2)).l ↑z1) ∧
  ∀ (z1 z2 : {z // IsASPLabel ((cop_sem p (bseq s c1 c2)).l z)}),
            f z1 = f z2 → z1 = z2 := by 
    simp at mem
    rw [QLPO.mem_seq_comp_iff] at mem
    rcases mem with ⟨la, lb, eq, ha, hb⟩
    change ⟦l1⟧ = ⟦la.earlier lb⟧ at eq
    simp at eq
    rcases eq with ⟨⟨e, he⟩, tmp⟩; clear tmp
    specialize @IH1 p la ha
    rcases IH1 with ⟨f, hf1, hf2, hf3⟩
    specialize @IH2 p lb hb
    rcases IH2 with ⟨g, hg1, hg2, hg3⟩
    --refine ⟨_, _, _, _⟩,
    use λ x => by 
      obtain ⟨x, hx⟩ := x; cases x with 
      | inl x => cases x; cases hx
      | inr x => cases x with 
        | inl x => cases x with
          | inl x => exact e.invFun (.inl (f ⟨x, hx⟩))
          | inr x => exact e.invFun (.inr (g ⟨x, hx⟩))
        | inr x => cases x; cases hx
    constructor
    · intro z1 z2
      obtain ⟨z1, hz1⟩ := z1; obtain ⟨z2, hz2⟩ := z2
      cases z1 with 
      | inl z1 => cases z1; cases hz1
      | inr z1 => cases z1 with
        | inl z1 => cases z2 with 
          | inl z2 => cases z2; cases hz2
          | inr z2 => cases z2 with
            | inl z2 => cases z1 with
              | inl z1 => cases z2 with
                | inl z2 => 
                  simp
                  constructor <;> intro le
                  · apply Sum.Lex.inr_mono
                    apply Sum.Lex.inl_mono
                    apply Sum.Lex.inl_mono 
                    apply Sum.Lex.inl_le_inl_iff.1 at le
                    exact (hf1 ⟨z1, hz1⟩ ⟨z2, hz2⟩).mp le                    
                  · apply Sum.Lex.inl_mono 
                    apply Sum.Lex.inr_le_inr_iff.1 at le 
                    apply Sum.Lex.inl_le_inl_iff.1 at le 
                    apply Sum.Lex.inl_le_inl_iff.1 at le 
                    exact (hf1 ⟨z1, hz1⟩ ⟨z2, hz2⟩).2 le
                | inr z2 => 
                  simp
                  constructor <;> intro _
                  · apply Sum.Lex.inr_mono
                    apply Sum.Lex.inl_mono 
                    apply Sum.Lex.inl_le_inr 
                  · apply Sum.Lex.inl_le_inr
              | inr z1 => cases z2 with 
                | inl z2 => 
                  simp
                  constructor <;> intro le 
                  · cases le
                  · apply Sum.Lex.inr_le_inr_iff.1 at le
                    apply Sum.Lex.inl_le_inl_iff.1 at le
                    cases le
                | inr z2 => 
                  simp
                  constructor <;> intro le
                  · apply Sum.Lex.inr_mono
                    apply Sum.Lex.inl_mono
                    apply Sum.Lex.inr_mono
                    apply Sum.Lex.inr_le_inr_iff.1 at le 
                    exact (hg1 ⟨z1, hz1⟩ ⟨z2, hz2⟩).1 le
                  · apply Sum.Lex.inr_mono
                    apply Sum.Lex.inr_le_inr_iff.1 at le
                    apply Sum.Lex.inl_le_inl_iff.1 at le 
                    apply Sum.Lex.inr_le_inr_iff.1 at le 
                    exact (hg1 ⟨z1, hz1⟩ ⟨z2, hz2⟩).2 le
            | inr z2 => cases z2; cases hz2 
        | inr z1 => cases z1; cases hz1 
    constructor 
    · intro z; obtain ⟨z, hz⟩ :=z;
      cases z with
      | inl z => cases hz
      | inr z => cases z with
        | inl z => cases z with 
          | inl z => rw [he]; simp; rw [hf2]
          | inr z => rw [he]; simp; rw [hg2]
        | inr z => cases hz
    · intro z1 z2 zeq
      obtain ⟨z1, hz1⟩ := z1; obtain ⟨z2, hz2⟩ := z2
      cases z1 with
      | inl z1 => cases z1; cases hz1
      | inr z1 => cases z1 with 
        | inl z1 => cases z1 with 
          | inl z1 => cases z2 with 
            | inl z2 => cases z2; cases hz2 
            | inr z2 => cases z2 with 
              | inl z2 => cases z2 with 
                | inl z2 => 
                  simp at zeq ⊢
                  congr
                  apply Sum.inl_injective at zeq
                  apply (hf3 ⟨z1, hz1⟩ ⟨z2, hz2⟩) at zeq
                  simp at zeq; exact zeq
                | inr z2 => simp at zeq
              | inr z2 => cases z2; cases hz2
          | inr z1 => cases z2 with 
            | inl z2 => cases z2; cases hz2
            | inr z2 => cases z2 with 
              | inl z2 => cases z2 with 
                | inl z2 => simp at zeq
                | inr z2 => 
                  simp at zeq ⊢
                  apply Sum.inr_injective at zeq
                  congr
                  apply (hg3 ⟨z1, hz1⟩ ⟨z2, hz2⟩) at zeq
                  simp at zeq; exact zeq
              | inr z2 => cases z2; cases hz2
        | inr z1 => cases z1; cases hz1

  lemma le_transfer_bpar (s : Split) (c1 c2 : Copland) {p : Place} (l1 : LPO Label)
  (IH1 : ∀ {p : Place} (l1 : LPO Label),
            ⟦l1⟧ ∈ BS (transfer c1) →
            (∃ (f : {z // IsASPLabel ((cop_sem p c1).l z)} → l1.t),
                (∀ (z1 z2 : {z // IsASPLabel ((cop_sem p c1).l z)}),
                    f z1 ≤ f z2 ↔ z1 ≤ z2) ∧
                  (∀ (z1 : {z // IsASPLabel ((cop_sem p c1).l z)}),
                      l1.l (f z1) = (cop_sem p c1).l ↑z1) ∧
                    ∀ (z1 z2 : {z // IsASPLabel ((cop_sem p c1).l z)}),
                      f z1 = f z2 → z1 = z2))
  (IH2 : ∀ {p : Place} (l1 : LPO Label),
            ⟦l1⟧ ∈ BS (transfer c2) →
            (∃ (f : {z // IsASPLabel ((cop_sem p c2).l z)} → l1.t),
                (∀ (z1 z2 : {z // IsASPLabel ((cop_sem p c2).l z)}),
                    f z1 ≤ f z2 ↔ z1 ≤ z2) ∧
                  (∀ (z1 : {z // IsASPLabel ((cop_sem p c2).l z)}),
                      l1.l (f z1) = (cop_sem p c2).l ↑z1) ∧
                    ∀ (z1 z2 : {z // IsASPLabel ((cop_sem p c2).l z)}),
                      f z1 = f z2 → z1 = z2))
  (mem : ⟦l1⟧ ∈ BS (transfer (bpar s c1 c2))) :
  ∃ (f : {z // IsASPLabel ((cop_sem p (bpar s c1 c2)).l z)} → l1.t),
  (∀ (z1 z2 : {z // IsASPLabel ((cop_sem p (bpar s c1 c2)).l z)}),
          f z1 ≤ f z2 ↔ z1 ≤ z2) ∧
  (∀ (z1 : {z // IsASPLabel ((cop_sem p (bpar s c1 c2)).l z)}),
            l1.l (f z1) = (cop_sem p (bpar s c1 c2)).l ↑z1) ∧
  ∀ (z1 z2 : {z // IsASPLabel ((cop_sem p (bpar s c1 c2)).l z)}),
            f z1 = f z2 → z1 = z2 := by 
    simp at mem
    rw [QLPO.mem_dist_prod_iff] at mem
    rcases mem with ⟨la, lb, eq, ha, hb⟩
    change ⟦l1⟧ = ⟦la.merge lb⟧ at eq
    simp at eq
    rcases eq with ⟨⟨e, he⟩, tmp⟩; clear tmp
    specialize @IH1 p la ha
    rcases IH1 with ⟨f, hf1, hf2, hf3⟩
    specialize @IH2 p lb hb
    rcases IH2 with ⟨g, hg1, hg2, hg3⟩
    --refine ⟨_, _, _, _⟩,
    use λ x => by 
      obtain ⟨x, hx⟩ := x 
      cases x with 
      | inl x => cases x; cases hx 
      | inr x => cases x with 
        | inl x => cases x with 
          | inl x => exact e.invFun (.inl (f ⟨x, hx⟩))
          | inr x => exact e.invFun (.inr (g ⟨x, hx⟩))
        | inr x => cases x; cases hx 
    constructor
    · intro z1 z2
      obtain ⟨z1, hz1⟩ := z1; obtain ⟨z2, hz2⟩ := z2
      cases z1 with 
      | inl z1 => cases z1; cases hz1
      | inr z1 => cases z1 with 
        | inl z1 => cases z1 with 
          | inl z1 => cases z2 with 
            | inl z2 => cases z2; cases hz2
            | inr z2 => cases z2 with 
              | inl z2 => cases z2 with 
                | inl z2 => 
                  simp
                  constructor <;> intro le
                  · apply Sum.Lex.inr_mono 
                    apply Sum.Lex.inl_mono 
                    apply Sum.inl_mono 
                    apply Sum.inl_le_inl_iff.1 at le 
                    exact (hf1 ⟨z1, hz1⟩ ⟨z2, hz2⟩).1 le
                  · apply Sum.inl_mono 
                    apply Sum.Lex.inr_le_inr_iff.1 at le 
                    apply Sum.Lex.inl_le_inl_iff.1 at le 
                    apply Sum.inl_le_inl_iff.1 at le 
                    exact (hf1 ⟨z1, hz1⟩ ⟨z2, hz2⟩).2 le
                | inr z2 => 
                  simp
                  constructor <;> intro le
                  · cases le
                  · apply Sum.Lex.inr_le_inr_iff.1 at le
                    apply Sum.Lex.inl_le_inl_iff.1 at le 
                    cases le
              | inr z2 => cases z2; cases hz2
          | inr z1 => cases z2 with 
            | inl z2 => cases z2; cases hz2 
            | inr z2 => cases z2 with 
              | inl z2 => cases z2 with 
                | inl z2 => 
                  simp
                  constructor <;> intro le
                  · cases le
                  · apply Sum.Lex.inr_le_inr_iff.1 at le
                    apply Sum.Lex.inl_le_inl_iff.1 at le 
                    cases le
                | inr z2 => 
                  simp
                  constructor <;> intro le
                  · apply Sum.Lex.inr_mono
                    apply Sum.Lex.inl_mono
                    apply Sum.inr_mono 
                    apply Sum.inr_le_inr_iff.1 at le 
                    exact (hg1 ⟨z1, hz1⟩ ⟨z2, hz2⟩).1 le
                  · apply Sum.inr_mono 
                    apply Sum.Lex.inr_le_inr_iff.1 at le
                    apply Sum.Lex.inl_le_inl_iff.1 at le 
                    apply Sum.inr_le_inr_iff.1 at le
                    exact (hg1 ⟨z1, hz1⟩ ⟨z2, hz2⟩).2 le
              | inr z2 => cases z2; cases hz2
        | inr z1 => cases z1; cases hz1
    constructor
    · intro z; obtain ⟨z, hz⟩ := z
      cases z with 
      | inl z => cases z; cases hz 
      | inr z => cases z with 
        | inl z => cases z with 
          | inl z => rw [he]; simp; rw [hf2]
          | inr z => rw [he]; simp; rw [hg2]
        | inr z => cases z; cases hz 
    · intro z1 z2 zeq
      obtain ⟨z1, hz1⟩ := z1; obtain ⟨z2, hz2⟩ := z2
      cases z1 with 
      | inl z1 => cases z1; cases hz1
      | inr z1 => cases z1 with 
        | inl z1 => cases z1 with 
          | inl z1 => cases z2 with 
            | inl z2 => cases z2; cases hz2
            | inr z2 => cases z2 with 
              | inl z2 => cases z2 with 
                | inl z2 => 
                  simp at zeq ⊢
                  congr
                  apply Sum.inl_injective at zeq
                  apply (hf3 ⟨z1, hz1⟩ ⟨z2, hz2⟩) at zeq 
                  simp at zeq; exact zeq
                | inr z2 => simp at zeq
              | inr z2 => cases z2; cases hz2 
          | inr z1 => cases z2 with 
            | inl z2 => cases z2; cases hz2
            | inr z2 => cases z2 with 
              | inl z2 => cases z2 with 
                | inl z2 => simp at zeq
                | inr z2 => 
                  simp at zeq ⊢
                  congr
                  apply Sum.inr_injective at zeq
                  apply (hg3 ⟨z1, hz1⟩ ⟨z2, hz2⟩) at zeq
                  simp at zeq; exact zeq 
              | inr z2 => cases z2; cases hz2 
        | inr z1 => cases z1; cases hz1 

  lemma le_transfer_att (q : Place) (c1 : Copland) {p : Place} (l1 : LPO Label)
  (IH1 : ∀ {p : Place} (l1 : LPO Label),
            ⟦l1⟧ ∈ BS (transfer c1) →
            (∃ (f : {z // IsASPLabel ((cop_sem p c1).l z)} → l1.t),
                (∀ (z1 z2 : {z // IsASPLabel ((cop_sem p c1).l z)}),
                    f z1 ≤ f z2 ↔ z1 ≤ z2) ∧
                  (∀ (z1 : {z // IsASPLabel ((cop_sem p c1).l z)}),
                      l1.l (f z1) = (cop_sem p c1).l ↑z1) ∧
                    ∀ (z1 z2 : {z // IsASPLabel ((cop_sem p c1).l z)}),
                      f z1 = f z2 → z1 = z2))
  (mem : ⟦l1⟧ ∈ BS (transfer (att q c1))) :
  ∃ (f : {z // IsASPLabel ((cop_sem p (att q c1)).l z)} → l1.t),
  (∀ (z1 z2 : {z // IsASPLabel ((cop_sem p (att q c1)).l z)}),
          f z1 ≤ f z2 ↔ z1 ≤ z2) ∧
  (∀ (z1 : {z // IsASPLabel ((cop_sem p (att q c1)).l z)}),
            l1.l (f z1) = (cop_sem p (att q c1)).l ↑z1) ∧
  ∀ (z1 z2 : {z // IsASPLabel ((cop_sem p (att q c1)).l z)}),
            f z1 = f z2 → z1 = z2 := by 
    simp at mem
    specialize @IH1 q l1 mem
    rcases IH1 with ⟨f, hf1, hf2, hf3⟩
    --refine ⟨_, _, _, _⟩,
    use λ x => by
      obtain ⟨x, hx⟩ := x
      cases x with 
      | inl x => cases x; cases hx
      | inr x => cases x with 
        | inl x => exact f ⟨x, hx⟩
        | inr x => cases x; cases hx
    constructor
    · intro z1 z2
      obtain ⟨z1, hz1⟩ := z1; obtain ⟨z2, hz2⟩ := z2
      cases z1 with 
      | inl z1 => cases z1; cases hz1
      | inr z1 => cases z1 with 
        | inl z1 => cases z2 with 
          | inl z2 => cases z2; cases hz2
          | inr z2 => cases z2 with 
            | inl z2 => 
              simp
              constructor <;> intro le
              · apply Sum.Lex.inr_mono 
                apply Sum.Lex.inl_mono
                exact (hf1 ⟨z1, hz1⟩ ⟨z2, hz2⟩).1 le 
              · apply Sum.Lex.inr_le_inr_iff.1 at le
                apply Sum.Lex.inl_le_inl_iff.1 at le 
                exact (hf1 ⟨z1, hz1⟩ ⟨z2, hz2⟩).2 le 
            | inr z2 => cases z2; cases hz2
        | inr z1 => cases z1; cases hz1
    constructor
    · intro z; obtain ⟨z, hz⟩ := z
      cases z with 
      | inl z => cases z; cases hz
      | inr z => cases z with 
        | inl z => simp; rw[hf2]
        | inr z => cases z; cases hz
    · intro z1 z2 zeq
      obtain ⟨z1, hz1⟩ := z1; obtain ⟨z2, hz2⟩ := z2
      cases z1 with 
      | inl z1 => cases z1; cases hz1
      | inr z1 => cases z1 with 
        | inl z1 => cases z2 with 
          | inl z2 => cases z2; cases hz2
          | inr z2 => cases z2 with 
            | inl z2 => 
              simp at zeq ⊢
              congr
              apply (hf3 ⟨z1, hz1⟩ ⟨z2, hz2⟩) at zeq
              simp at zeq; exact zeq
            | inr z2 => cases z2; cases hz2
        | inr z1 => cases z1; cases hz1

end inductive_cases

/- 
  This is a partial converse to transfer_le above. 
  Given a Copland phrase c and an element l1 of the semantics of
  its corresponding attack tree (there will only be one such element),
  we construct an injective function from ASP events in the Copland semantics
  to events of l1 such that order and labels are preserved and no orders
  between events are added. 
-/
lemma le_transfer :
∀ c l1,
⟦l1⟧ ∈ BS (transfer c) → 
∃ f : { z : (cop_sem p c).t // IsASPLabel ((cop_sem p c).l z) } → l1.t,
(∀ z1 z2, f z1 ≤ f z2 ↔ z1 ≤ z2) ∧ 
(∀ z1, l1.l (f z1) = (cop_sem p c).l z1) ∧
(∀ z1 z2, f z1 = f z2 → z1 = z2) := by 
  intro c
  revert p; induction' c <;> intro p l1 mem
  case atom a 
  · exact le_transfer_atom a l1 mem
  case lseq c1 c2 IH1 IH2
  · exact le_transfer_lseq c1 c2 l1 @IH1 @IH2 mem
  case bseq s c1 c2 IH1 IH2
  · exact le_transfer_bseq s c1 c2 l1 @IH1 @IH2 mem
  case bpar s c1 c2 IH1 IH2
  · exact le_transfer_bpar s c1 c2 l1 @IH1 @IH2 mem
  case att q c1 IH1
  · exact le_transfer_att q c1 l1 @IH1 mem

-- If a function preserves labels, it preserves whether or not
-- a Label is an ASP Label. (Doesn't belong here, but not sure
-- where its natural home is.)
lemma preserves_is_asp_label {l1 l2 : LPO Label} 
{f : l1.t → l2.t} (hf : ∀ a, l1.l a = l2.l (f a)) {a} :
IsASPLabel (l1.l a) ↔ IsASPLabel (l2.l (f a)) := by
  specialize hf a
  cases h : l1.l a
  all_goals
    constructor
    · intro lab; rw [←hf, h]; exact lab 
    · intro lab; rw [←hf, h] at lab; exact lab

-- Given a base function from atomic Copland phrases to a domain
-- of interpretation, this is the corresponding function on 
-- atomic attack trees. 
@[simp]
def V1 {Vals : Type} [Inhabited Vals] (V : Copland → Vals) : 
  AttackTree Label → Vals 
| (atm (Label.msp c1 c2)) => V (atom (ASP.msp c1 c2))
--| (atm (Label.nul)) => V (atom (ASP.nul))
| (atm (Label.cpy)) => V (atom (ASP.cpy))
| (atm (Label.hsh)) => V (atom (ASP.hsh))
| (atm (Label.sig)) => V (atom (ASP.sig))
| _ => default 

section 
namespace Supports
open Supports 

--local attribute [reducible] att_sup CopSup 
local instance : Preorder (AttackTree Lab) := AT.supports_preorder Lab

local instance : Preorder (Copland_p p) := Copland.supports_preorder p 

-- If two Copland phrases are ordered by Supports, then
-- their corrsponding attack trees are ordered the same way. 
lemma transfer_le_of_le {p} {c1 c2 : Copland_p p} (le : c1 ≤ c2) :
transfer c1 ≤ transfer c2 := by
  rw [AT.le_def]
  intro D Dmem
  obtain ⟨A, Amem⟩ := BS_exists_qlpo (transfer c2)
  use A, Amem
  rw [Cop.le_def] at le
  obtain ⟨C, Cmem⟩ := copland_base_sem_exists_qlpo p c1
  specialize le C Cmem
  rcases le with ⟨B, Bmem, le⟩
  simp at Cmem Bmem
  have AleB := transfer_le p Amem; rw [←Bmem] at AleB
  have AleC := le_trans AleB le
  revert Dmem le Cmem AleB AleC Amem Bmem 
  --revert A C D; intro A C D
  refine Quotient.inductionOn₃ A C D fun 
  | a, c, d => by
    intro dmem amem _ cdef _ _ alec
    obtain ⟨f, hf⟩ := alec
    have g := @le_transfer p c1 d dmem
    rcases g with ⟨g, hg1, hg2, hg3⟩
    rw [Quotient.eq] at cdef
    rcases cdef with ⟨⟨e, he⟩, tmp⟩; clear tmp
    fconstructor
    --refine ⟨λ x => g ⟨e.toFun (f x), _⟩, _⟩,
    use λ x => g ⟨e.toFun (f x), by
      have xlab := transfer_label p c2 x amem
      rw [←preserves_is_asp_label he]
      rw [←preserves_is_asp_label hf.2.1]
      exact xlab⟩
    constructor
    · intro z1 z2 lez
      replace lez := hf.1 lez
      rw [←e.map_rel_iff] at lez
      rw [hg1]; exact lez
    constructor
    · intro z
      rw [hf.2.1, he, hg2]
    · intro z1 z2 zeq
      replace zeq := hg3 ⟨e.toEquiv.toFun (f z1), _⟩ ⟨e.toEquiv.toFun (f z2), _⟩ zeq
      simp at zeq
      exact hf.2.2 zeq

end Supports 
end 

section 
namespace Covers
open Covers 

--local attribute [reducible] att_cov cop_cov
local instance : Preorder (AttackTree lab) := AT.covers_preorder lab 

local instance : Preorder (Copland_p p) := Copland.covers_preorder p 

-- If two Copland phrases are ordered by Covers, then
-- their corresponding attack trees are ordered the same way. 
lemma transfer_le_of_le {p} {c1 c2 : Copland_p p} (le : c1 ≤ c2) :
transfer c1 ≤ transfer c2 := by 
  rw [AT.le_def]
  intro D Dmem
  obtain ⟨A, Amem⟩ := BS_exists_qlpo (transfer c2)
  use A, Amem
  rw [Cop.le_def] at le
  obtain ⟨C, Cmem⟩ := copland_base_sem_exists_qlpo p c1
  specialize le C Cmem
  rcases le with ⟨B, Bmem, CleB⟩
  simp at Cmem Bmem
  have DleC := transfer_le p Dmem; rw [←Cmem] at DleC
  have DleB := le_trans DleC CleB
  --revert D B A, intros D B A,
  revert Dmem Amem Bmem CleB DleC DleB
  refine Quotient.inductionOn₃ D B A fun 
  | d, b, a => by
    intros dmem amem _ bdef _ dleb
    obtain ⟨f, hf⟩ := dleb
    have g := @le_transfer p c2 a amem
    rcases g with ⟨g, hg1, hg2, hg3⟩
    rw [Quotient.eq] at bdef
    rcases bdef with ⟨⟨e, he⟩, tmp⟩; clear tmp
    use λ x => g ⟨e.toFun (f x), by
      have xlab := transfer_label p c1 x dmem 
      rw [←preserves_is_asp_label he]
      rw [←preserves_is_asp_label hf.2.1]
      exact xlab⟩
    constructor
    · intro z1 z2 lez
      replace lez := hf.1 lez
      rw [←e.map_rel_iff] at lez
      rw [hg1]; exact lez
    constructor
    · intro z
      rw [hf.2.1, he, hg2]
    · intro z1 z2 zeq
      replace zeq := hg3 ⟨e.toEquiv.toFun (f z1), _⟩ ⟨e.toEquiv.toFun (f z2), _⟩ zeq
      simp at zeq
      exact hf.2.2 zeq

end Covers 
end 

-- Scratch paper below here. 
-- Trying to show in general that contra- and co-variant soundness
-- of attack trees imply the same soundness for Copland phrases. 
--variables (D : Type) (att_ops : Vector (D → D → D) 3)

@[simp]
def ops_compat {D} (att_ops cop_ops : Vector (D → D → D) 3) :=
Vector.get att_ops 1 = cop_ops.head ∧ 
Vector.get att_ops 2 = Vector.get cop_ops 1 ∧ 
Vector.get att_ops 2 = Vector.get cop_ops 2

variable {D : Type}
variable (att_ops cop_ops : Vector (D → D → D) 3)

@[simp]
lemma aad_atm {a} (V : AttackTree Label → D) : 
att_ad att_ops V (atm a) = V (atm a) := by rfl 

@[simp]
lemma aad_or {t1 t2} (V : AttackTree Label → D) {f1}
(h1 : Vector.get att_ops 0 = f1):
att_ad att_ops V (or t1 t2) = 
  f1 (att_ad att_ops V t1) (att_ad att_ops V t2) := by subst_vars; rfl

@[simp]
lemma aad_and {t1 t2} (V : AttackTree Lab → D) {f2} 
(h2 : Vector.get att_ops 1 = f2): 
att_ad att_ops V (and t1 t2) = 
  f2 (att_ad att_ops V t1) (att_ad att_ops V t2) := by subst_vars; rfl 

@[simp]
lemma aad_seq {t1 t2} (V : AttackTree Lab → D) {f3} 
(h3 : Vector.get att_ops 2 = f3): 
att_ad att_ops V (seq t1 t2) = 
  f3 (att_ad att_ops V t1) (att_ad att_ops V t2) := by subst_vars; rfl 

@[simp]
lemma cad_atom {a p} (V : Copland_p p → D) :
cop_ad id cop_ops V (atom a) = V (atom a) := by rfl 

@[simp]
lemma cad_bpar {p s c1 c2} (V : Copland_p p → D) {f1}
(h1 : Vector.get cop_ops 0 = f1):
cop_ad id cop_ops V (bpar s c1 c2) = 
 f1 (cop_ad id cop_ops V c1) (cop_ad id cop_ops V c2) := by subst_vars; rfl 

@[simp]
lemma cad_lseq {p c1 c2} (V : Copland_p p → D) {f2}
(h2 : Vector.get cop_ops 1 = f2):
cop_ad id cop_ops V (lseq c1 c2) = 
  f2 (cop_ad id cop_ops V c1) (cop_ad id cop_ops V c2) := by subst_vars; rfl 

@[simp]
lemma cad_bseq {p s c1 c2} (V : Copland_p p → D) {f3}
(h2 : Vector.get cop_ops 2 = f3):
cop_ad id cop_ops V (bseq s c1 c2) = 
  f3 (cop_ad id cop_ops V c1) (cop_ad id cop_ops V c2) := by subst_vars; rfl 

@[simp]
lemma cad_att {p q c1} (V : Copland_p p → D) : 
cop_ad id cop_ops V (att q c1) = cop_ad id cop_ops V c1 := by rfl 

lemma eval_eq {p} {c} {att_ops cop_ops : Vector (D → D → D) 3} 
{V : Copland_p p → D} [Inhabited D] 
(cmpt : ops_compat att_ops cop_ops):
cop_ad id cop_ops V c = att_ad att_ops (V1 V) (transfer c) := by 
  revert V
  induction' c <;> intro p
  case atom a
  · cases a <;> simp [asp_label]
  case lseq c1 c2 IH1 IH2
  · simp only [cop_ad, att_ad, transfer]
    rw [←cmpt.2.1, IH1, IH2]
  case bseq s c1 c2 IH1 IH2
  · simp only [cop_ad, att_ad, transfer]
    rw [←cmpt.2.2, IH1, IH2]
  case bpar s c1 c2 IH1 IH2
  · simp only [cop_ad, att_ad, transfer, Vector.get_zero]
    rw [←cmpt.1, IH1, IH2]
  case att q c1 IH1
  · simp only [transfer, cad_att]
    rw [IH1]

section 
namespace Supports 

local instance : Preorder (Copland_p p) := Copland.supports_preorder p  
local instance : Preorder (AttackTree Label) := AT.supports_preorder Label 

--local attribute [reducible] Copland_p

-- Contravariant soundness for attack trees implies contravariant
-- soundness for Copland phrases. 
lemma is_contra_sound (p) --(V : Copland_p p → D) 
[Inhabited D] [Preorder D]
(cmpt : ops_compat att_ops cop_ops): 
contra_sound (@att_ad Label D att_ops) → contra_sound (@cop_ad p D id cop_ops) := by
  unfold contra_sound
  rintro AT_sound c1 c2 V le
  specialize AT_sound (transfer c1) (transfer c2)
  specialize AT_sound (V1 V) (transfer_le_of_le le)
  rw [eval_eq cmpt]
  rw [eval_eq cmpt]
  exact AT_sound

-- Covariant soundness for attack trees implies covariant
-- soundness for Copland phrases. 
lemma is_co_sound (p) --(V : Copland_p p → D) 
[Inhabited D] [Preorder D]
(cmpt : ops_compat att_ops cop_ops) : 
co_sound (@att_ad Label D att_ops) → co_sound (@cop_ad p D id cop_ops) := by
  unfold co_sound
  rintro AT_sound c1 c2 V le
  specialize AT_sound (transfer c1) (transfer c2)
  specialize AT_sound (V1 V) (transfer_le_of_le le)
  rw [eval_eq cmpt]
  rw [eval_eq cmpt]
  exact AT_sound

section mat 
/- 
  This section pertains to the attribute domain interpreted as 
  "Minimum Attack Time (MAT)."

  We show that, if attack trees are sound with respect to this 
  attribute domain then Copland phrases are sound (in the same 
  direction). 
-/

  -- The mat operators for attack trees. 
  @[simp]
  noncomputable
  def mat_att_ops : Vector (ℝ → ℝ → ℝ) 3 := 
  ⟨[(λ a b => min a b), (λ a b => max a b), (λ a b => a + b)], by simp⟩ 

  -- The mat operators for Copland phrases. 
  @[simp]
  noncomputable
  def mat_cop_ops : Vector (ℝ → ℝ → ℝ) 3 :=
  ⟨[λ a b => max a b, λ a b => a + b, λ a b => a + b], by simp⟩

  -- We must show these operators are compatible. 
  lemma mat_compat : ops_compat mat_att_ops mat_cop_ops := by 
    exact { left := rfl, right := { left := rfl, right := rfl } }

  -- Copland is contravariantly sound under these operators if 
  -- attack trees are. 
  lemma is_mat_contra_sound :
  contra_sound (@att_ad Label ℝ mat_att_ops) → 
  contra_sound (@cop_ad p ℝ id mat_cop_ops) := by 
    exact is_contra_sound mat_att_ops mat_cop_ops p mat_compat
  
  -- Copland is covariantly sound under these operators if 
  -- attack trees are. 
  lemma is_mat_co_sound : 
  co_sound (@att_ad Label ℝ mat_att_ops) → co_sound (@cop_ad p ℝ id mat_cop_ops) := by
    exact is_co_sound mat_att_ops mat_cop_ops p mat_compat

end mat 

section mer 
/- 
  This file pertains to the attribute domain interpreted as 
  "Minimum # of Experts Required to counter an attack (MER)."

  We show that, if attack trees are sound with respect to this 
  attribute domain then Copland phrases are sound (in the same 
  direction). 
-/

  -- The mer operators for attack trees. 
  @[simp]
  def mer_att_ops : Vector (ℕ → ℕ → ℕ) 3 := 
  ⟨[(λ a b => min a b), (λ a b => a + b), (λ a b => max a b)], by simp⟩ 

  -- The mer perators for Copland phrases. 
  @[simp]
  def mer_cop_ops : Vector (ℕ → ℕ → ℕ) 3 :=
  ⟨[λ a b => a + b, λ a b => max a b, λ a b => max a b], by simp⟩

  -- These operators are compatible. 
  lemma mer_compat : ops_compat mer_att_ops mer_cop_ops := by 
    exact { left := rfl, right := { left := rfl, right := rfl } }

  -- Copland is contravariantly sound under these operators if 
  -- attack trees are. 
  lemma is_mer_contra_sound : 
  contra_sound (@att_ad Label ℕ mer_att_ops) → 
  contra_sound (@cop_ad p ℕ id mer_cop_ops) := by 
    exact is_contra_sound mer_att_ops mer_cop_ops p mer_compat

  -- Copland is covariantly sound under these operators if 
  -- attack trees are. 
  lemma is_mer_co_sound : 
  co_sound (@att_ad Label ℕ mer_att_ops) → co_sound (@cop_ad p ℕ id mer_cop_ops) := by
    exact is_co_sound mer_att_ops mer_cop_ops p mer_compat

end mer 
end Supports
end 

section 
namespace Covers 

local instance : Preorder (Copland_p p) := Copland.covers_preorder p  
local instance : Preorder (AttackTree Label) := AT.covers_preorder Label 

--local attribute [reducible] Copland_p

-- Contravariant soundness for attack trees implies contravariant
-- soundness for Copland phrases. 
lemma is_contra_sound (p) 
[Inhabited D] [Preorder D]
(cmpt : ops_compat att_ops cop_ops): 
contra_sound (@att_ad Label D att_ops) → contra_sound (@cop_ad p D id cop_ops) := by
  unfold contra_sound
  rintro AT_sound c1 c2 V le
  specialize AT_sound (transfer c1) (transfer c2)
  specialize AT_sound (V1 V) (transfer_le_of_le le)
  rw [eval_eq cmpt]
  rw [eval_eq cmpt]
  exact AT_sound

-- Covariant soundness for attack trees implies covariant
-- soundness for Copland phrases. 
lemma is_co_sound (p) 
[Inhabited D] [Preorder D]
(cmpt : ops_compat att_ops cop_ops) : 
co_sound (@att_ad Label D att_ops) → co_sound (@cop_ad p D id cop_ops) := by 
  unfold co_sound
  rintro AT_sound c1 c2 V le
  specialize AT_sound (transfer c1) (transfer c2)
  specialize AT_sound (V1 V) (transfer_le_of_le le)
  rw [eval_eq cmpt]
  rw [eval_eq cmpt] 
  exact AT_sound

section gnca
  /- 
    This section pertains to the attribute domain interpreted as 
    "Guards Necessary to Counter an Attack (GNCA)". 

    We show that, if attack trees are sound with respect to this 
    attribute domain then Copland phrases are sound (in the same 
    direction). 
  -/

  -- Vector defining the gnca operators for attack trees. 
  @[simp]
  def gnca_att_ops : Vector (ℕ → ℕ → ℕ) 3 := 
  ⟨[(λ a b => max a b), (λ a b => a + b), (λ a b => max a b)], by simp⟩ 

  -- Vector defining the operators for Copland phrases 
  @[simp]
  def gnca_cop_ops : Vector (ℕ → ℕ → ℕ) 3 :=
  ⟨[λ a b => a + b, λ a b => max a b, λ a b => max a b], by simp⟩

  -- These operator lists are compatible. 
  lemma gnca_compat : ops_compat gnca_att_ops gnca_cop_ops := by 
    exact { left := rfl, right := { left := rfl, right := rfl } }

  -- Contravariant soundness for attack trees implies contravariant
  -- soundness for Copland phrases 
  lemma is_gnca_contra_sound : 
  contra_sound (@att_ad Label ℕ gnca_att_ops) → 
  contra_sound (@cop_ad p ℕ id gnca_cop_ops) := by 
    exact is_contra_sound gnca_att_ops gnca_cop_ops p gnca_compat
  
  -- Covariant soundness for attack trees implies covariant soundness
  -- for Copland phrases
  lemma is_gnca_co_sound : 
  co_sound (@att_ad Label ℕ gnca_att_ops) → 
  co_sound (@cop_ad p ℕ id gnca_cop_ops) := by 
    exact is_co_sound gnca_att_ops gnca_cop_ops p gnca_compat
    
end gnca 

section traa 
/- 
  This section pertains to the attribute domain interpreted as 
  "Time Required for All Attacks (TRAA)."

  We show that, if attack trees are sound with respect to this 
  attribute domain then Copland phrases are sound (in the same 
  direction). 
-/

  -- The traa operators for attack trees. 
  @[simp]
  noncomputable
  def traa_att_ops : Vector (ℝ → ℝ → ℝ) 3 := 
  ⟨[(λ a b => max a b), (λ a b => max a b), (λ a b => a + b)], by simp⟩ 

  -- The traa operators for Copland phrases. 
  @[simp]
  noncomputable
  def traa_cop_ops : Vector (ℝ → ℝ → ℝ) 3 :=
  ⟨[λ a b => max a b, λ a b => a + b, λ a b => a + b], by simp⟩  

  -- These operators are compatible. 
  lemma traa_compat : ops_compat traa_att_ops traa_cop_ops := by 
    exact { left := rfl, right := { left := rfl, right := rfl } }


  -- Copland is contravariantly sound under these operators if 
  -- attack trees are. 
  lemma is_traa_contra_sound : 
  contra_sound (@att_ad Label ℝ traa_att_ops) → 
  contra_sound (@cop_ad p ℝ id traa_cop_ops) := by 
    exact is_contra_sound traa_att_ops traa_cop_ops p traa_compat

  -- Copland is covariantly sound under these operators if 
  -- attack trees are. 
  lemma is_traa_co_sound : 
  co_sound (@att_ad Label ℝ traa_att_ops) → 
  co_sound (@cop_ad p ℝ id traa_cop_ops) := by 
    exact is_co_sound traa_att_ops traa_cop_ops p traa_compat
    
end traa 
end Covers 
end 
