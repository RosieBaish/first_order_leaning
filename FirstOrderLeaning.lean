open Classical

theorem forall_to_exists (p : Store → Heap → Heap → Prop) (f : ¬ ∀ s h h', ¬ (p s h h') ) : ∃ s h h', (p s h h') :=
  byContradiction
    (fun hyp1 : ¬ ∃ s h h', p s h h' =>
      have hyp2 : ∀ s h h', ¬ p s h h' :=
        fun s h h' =>
        fun hyp3 : p s h h' =>
        have hyp4 : ∃ s h h', p s h h' := ⟨ s , ⟨ h , ⟨h', hyp3⟩ ⟩ ⟩
        show False from hyp1 hyp4
      show False from f hyp2)

def dne {p} (hyp : ¬¬p) : p :=
  byContradiction
    (fun hyp1 : ¬p =>
     show False from hyp hyp1)

def dna {p} (hp : p) : ¬¬p :=
  λ hnp => False.elim (hnp hp)

theorem dne_equivalence {p}: ¬¬p ↔ p := by
  apply Iff.intro
  case mp =>  intro nnp; exact (dne nnp)
  case mpr => intro p; exact (dna p)

theorem dna_equivalence {p}: p ↔ ¬¬p:= by
  apply Iff.intro
  case mp => intro p; exact (dna p)
  case mpr =>  intro nnp; exact (dne nnp)


theorem exists_n_implies_n_forall {p : α → Prop} : (∃ x , ¬ p x) → (¬ ∀ x , p x) := by 
  intro ⟨ x, not_p_x ⟩
  intro for_all 
  have p_x := for_all x
  exact not_p_x p_x

theorem exists_implies_n_forall_n {p : α → Prop} : (∃ x , p x) → (¬ ∀ x , ¬ p x) := by 
  intro ⟨ x, p_x ⟩
  intro for_all 
  have not_p_x := for_all x
  exact not_p_x p_x

theorem forall_implies_n_exists_n {p : α → Prop} : (∀ x , p x) → ¬(∃ x , ¬ p x) := by 
  intro for_all
  intro ⟨ x, not_p_x ⟩
  have p_x := for_all x
  exact not_p_x p_x

theorem forall_n_implies_n_exists {p : α → Prop} : (∀ x , ¬ p x) → ¬(∃ x , p x) := by 
  intro for_all
  intro ⟨ x, p_x ⟩
  have not_p_x := for_all x
  exact not_p_x p_x

theorem pp_imp_nn {A B : Prop} : (A → B) ↔ ((¬B) → (¬A)) := by
  apply Iff.intro
  case mp  => 
    intro a_to_b
    intro not_b 
    intro a
    have b := a_to_b a
    exact not_b b
  case mpr =>
    intro nb_to_na
    intro a 
    apply byContradiction (
      λ not_b => by
      have not_a := nb_to_na not_b
      exact not_a a
    )

theorem np_imp_pn {A B : Prop} : ((¬A) → B) ↔ ((¬B) → A) := by
  apply Iff.intro
  case mp  => 
    conv =>
      lhs
      rw [pp_imp_nn] 
    intro nb_to_nna
    intro not_b 
    have nna := nb_to_nna not_b
    exact (dne nna)
  case mpr =>
    intro nb_to_a
    intro not_a 
    apply byContradiction (
      λ not_b => by
      have a := nb_to_a not_b
      exact not_a a
    )

theorem pn_imp_np {A B : Prop} : (A → (¬B)) ↔ (B → (¬A)) := by
  apply Iff.intro
  case mp  => 
    conv =>
      lhs
      rw [pp_imp_nn] 
    intro nnb_to_na
    intro b
    have nnb := (dna b)
    exact nnb_to_na nnb
  case mpr =>
    intro b_to_na
    intro a 
    apply byContradiction (
      λ nnb => by
      have not_a := b_to_na (dne nnb)
      exact not_a a
    )


theorem n_imp {P Q : Prop} : ((¬ P) → Q) ↔ (P ∨ Q) := by
  apply Iff.intro
  case mp  =>
    intro not_p_imp_q
    have p_or_not_p := em P
    apply Or.elim p_or_not_p 
      (
        λ p => Or.inl p
      )
      (
        λ np => Or.inr (not_p_imp_q np)
      )
  case mpr =>
    intro p_or_q
    cases p_or_q with
    | inl p =>
      intro np
      apply absurd p np
    | inr q => intro; exact q

theorem n_forall_implies_exists_n {p : α → Prop} : ¬(∀ x , p x) → (∃ x , ¬ p x) := by 
  rw [n_imp]
  apply Or.elim (em (∃ x , ¬ p x ))
    (
      λ exist => Or.inr exist
    )
    (
      λ x => sorry --match x with
        --| ¬ ⟨ not_exist, a ⟩  => sorry
    )

theorem exists_same_as_forall {p : α → Prop} : (∃ x , ¬ p x) ↔ (¬ ∀ x , p x) := by 
  apply Iff.intro
  case mp => apply exists_n_implies_n_forall
  case mpr => sorry
