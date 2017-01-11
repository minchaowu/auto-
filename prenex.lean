open classical tactic expr list

section prop_equivalence

  local attribute [instance] prop_decidable
  variables {a b : Prop}

  theorem not_not_iff (a : Prop) : ¬¬a ↔ a :=
  iff.intro classical.by_contradiction not_not_intro

  theorem implies_iff_not_or (a b : Prop) : (a → b) ↔ (¬ a ∨ b) :=
  iff.intro
    (λ h, if ha : a then or.inr (h ha) else or.inl ha)
    (λ h, or.elim h (λ hna ha, absurd ha hna) (λ hb ha, hb))

  theorem not_and_of_not_or_not (h : ¬ a ∨ ¬ b) : ¬ (a ∧ b) :=
  assume ⟨ha, hb⟩, or.elim h (assume hna, hna ha) (assume hnb, hnb hb)

  theorem not_or_not_of_not_and (h : ¬ (a ∧ b)) : ¬ a ∨ ¬ b :=
  if ha : a then
    or.inr (show ¬ b, from assume hb, h ⟨ha, hb⟩)
  else
    or.inl ha

  theorem not_and_iff (a b : Prop) : ¬ (a ∧ b) ↔ ¬a ∨ ¬b :=
  iff.intro not_or_not_of_not_and not_and_of_not_or_not

  theorem not_or_of_not_and_not (h : ¬ a ∧ ¬ b) : ¬ (a ∨ b) :=
  assume h₁, or.elim h₁ (assume ha, h^.left ha) (assume hb, h^.right hb)

  theorem not_and_not_of_not_or (h : ¬ (a ∨ b)) : ¬ a ∧ ¬ b :=
  and.intro (assume ha, h (or.inl ha)) (assume hb, h (or.inr hb))

  theorem not_or_iff (a b : Prop) : ¬ (a ∨ b) ↔ ¬ a ∧ ¬ b :=
  iff.intro not_and_not_of_not_or not_or_of_not_and_not

  theorem iff_eq (a b : Prop) : (a ↔ b) = ((a → b) ∧ (b → a)) := rfl

  check and.comm
  check or.comm

end prop_equivalence

section prenex_equivalence

  variables {A : Type}
  variables {p : Prop}
  variables {q : A → Prop}
  variable [inhabited A]

  theorem forall_not_of_not_exists : (¬ ∃ x, q x) → ∀ x, ¬ q x := 
  λ h x hqx, h (exists.intro x hqx)

  theorem exists_not_of_not_forall : (¬ ∀ x, q x) → ∃ x, ¬ q x := 
  λ h, by_contradiction
  (λ neg, have ∀ x, ¬ ¬ q x, from forall_not_of_not_exists neg, 
    have ∀ x, q x, from λ x, iff.elim_left (not_not_iff (q x)) (this x),
  show _, from h this)

  theorem forall_p_iff_p : (∀ x : A, p) ↔ p := 
  iff.intro (λ h, h (default A)) (λ h x, h)

  theorem exists_p_iff_p : (∃ x : A, p) ↔ p := 
  iff.intro (λ h, exists.elim h (λ x hx, hx)) (λ h, exists.intro (default A) h)

  theorem forall_of_forall_and_left : (∀ x, q x) ∧ p ↔ ∀ x, q x ∧ p := 
  iff.intro (λ h x, and.intro (h^.left x) h^.right) 
  (λ h, and.intro (λ x, (h x)^.left) (h (default A))^.right)

  theorem forall_of_forall_and_right : p ∧ (∀ x, q x) ↔ ∀ x, q x ∧ p := 
  iff.trans and.comm forall_of_forall_and_left

  theorem forall_of_forall_or_left : (∀ x, q x) ∨ p ↔ ∀ x, q x ∨ p := 
  iff.intro (λ h x, or.elim h (λ l, or.inl (l x)) (λ r, or.inr r)) 
  (λ h, or.elim (em p) (λ l, or.inr l) (λ r, or.inl (λ x, or.resolve_right (h x) r)))

  theorem forall_of_forall_or_right : p ∨ (∀ x, q x) ↔ ∀ x, q x ∨ p := 
  iff.trans or.comm forall_of_forall_or_left

  theorem exists_of_exists_and_left : (∃ x, q x) ∧ p ↔ ∃ x, q x ∧ p := 
  iff.intro (λ h, exists.elim h^.left (λ x hx, exists.intro x (and.intro hx h^.right)) ) 
  (λ h, exists.elim h (λ x hx, and.intro (exists.intro x hx^.left) hx^.right))

  theorem exists_of_exists_and_right : p ∧ (∃ x, q x) ↔ ∃ x, q x ∧ p := 
  iff.trans and.comm exists_of_exists_and_left

  theorem exists_of_exists_or_left : (∃ x, q x) ∨ p ↔ ∃ x, q x ∨ p := 
  iff.intro (λ h, or.elim h (λ l, exists.elim l (λ x hx, exists.intro x (or.inl hx))) 
    (λ r, exists.intro (default A) (or.inr r))) 
  (λ h, exists.elim h (λ x hx, or.elim hx (λ l, or.inl (exists.intro x l)) (λ r, or.inr r)))

  theorem exists_of_exists_or_right : p ∨ (∃ x, q x) ↔ ∃ x, q x ∨ p := 
  iff.trans or.comm exists_of_exists_or_left

end prenex_equivalence

meta def nnf_lemmas : list name := [``forall_not_of_not_exists, ``exists_not_of_not_forall, 
                                ``iff_eq, ``implies_iff_not_or, ``not_and_iff, ``not_or_iff, 
                                ``not_not_iff, ``not_true_iff, ``not_false_iff]

meta def normalize_hyp (lemmas : list expr) (hyp : expr) : tactic unit :=
do try (simp_at_using lemmas hyp)

meta def nnf_hyps : tactic unit :=
do hyps ← local_context,
   lemmas ← monad.mapm mk_const nnf_lemmas,
   monad.for' hyps (normalize_hyp lemmas)

meta def pnf_lemmas : list name := [``forall_p_iff_p, ``exists_p_iff_p, ``forall_of_forall_and_left, 
                             ``forall_of_forall_and_right, ``forall_of_forall_or_left, 
                             ``forall_of_forall_or_right, ``exists_of_exists_and_left, 
                             ``exists_of_exists_and_right, ``exists_of_exists_or_left, ``exists_of_exists_or_right]

meta def pnf_hyps : tactic unit :=
do hyps ← local_context,
   pnf_lemmas ← monad.mapm mk_const pnf_lemmas,
   monad.for' hyps (normalize_hyp pnf_lemmas)

example (p q r : Prop) (h₁ : ¬ (p ↔ (q ∧ ¬ r))) (h₂ : ¬ (p → (q → ¬ r))) : true :=
by do nnf_hyps,
      trace_state,
      triv

-- TODO: think about the order of applying simp rules.

example (A : Type) (p : Prop) (q : A → Prop) (h₁ : ¬ p → ((∀ x, q x) → p)) [inhabited A] : true :=
by do nnf_hyps,
      trace_state,
      pnf_hyps,
      trace_state,
      triv

print simplify

