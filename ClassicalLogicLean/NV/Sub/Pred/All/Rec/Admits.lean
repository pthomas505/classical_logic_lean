import ClassicalLogicLean.NV.Sub.Pred.All.Rec.Replace
import ClassicalLogicLean.NV.Sub.Var.All.Rec.Admits


set_option linter.style.docString false
set_option linter.style.emptyLine false
set_option linter.style.longLine false


namespace FOL.NV.Sub.Pred.All.Rec

open Formula_


-- multiple

/--
  Helper function for `admits_pred_all_rec`.
-/
def admits_pred_all_rec_aux
  (τ : PredName_ → ℕ → List VarName_ × Formula_)
  (binders : Finset VarName_) :
  Formula_ → Prop
  | pred_const_ _ _ => True
  | pred_var_ X xs =>
    let zs := (τ X xs.length).fst
    let H := (τ X xs.length).snd
    Sub.Var.All.Rec.admits_var_all_rec (Function.updateFromPairOfListsITE id zs xs) H ∧ (∀ x : VarName_, x ∈ binders → ¬ (var_is_free_in x H ∧ x ∉ zs)) ∧ xs.length = zs.length
  | true_ => True
  | false_ => True
  | eq_ _ _ => True
  | not_ phi => admits_pred_all_rec_aux τ binders phi
  | imp_ phi psi =>
      admits_pred_all_rec_aux τ binders phi ∧
      admits_pred_all_rec_aux τ binders psi
  | and_ phi psi =>
      admits_pred_all_rec_aux τ binders phi ∧
      admits_pred_all_rec_aux τ binders psi
  | or_ phi psi =>
      admits_pred_all_rec_aux τ binders phi ∧
      admits_pred_all_rec_aux τ binders psi
  | iff_ phi psi =>
      admits_pred_all_rec_aux τ binders phi ∧
      admits_pred_all_rec_aux τ binders psi
  | forall_ x phi => admits_pred_all_rec_aux τ (binders ∪ {x}) phi
  | exists_ x phi => admits_pred_all_rec_aux τ (binders ∪ {x}) phi
  | def_ _ _ => True

instance
  (τ : PredName_ → ℕ → List VarName_ × Formula_)
  (binders : Finset VarName_)
  (F : Formula_) :
  Decidable (admits_pred_all_rec_aux τ binders F) :=
  by
  induction F generalizing binders
  all_goals
    simp only [admits_pred_all_rec_aux]
    infer_instance


def admits_pred_all_rec
  (τ : PredName_ → ℕ → List VarName_ × Formula_)
  (F : Formula_) :
  Prop :=
  admits_pred_all_rec_aux τ ∅ F

instance
  (τ : PredName_ → ℕ → List VarName_ × Formula_)
  (F : Formula_) :
  Decidable (admits_pred_all_rec τ F) :=
  by
  simp only [admits_pred_all_rec]
  infer_instance


theorem substitution_theorem_admits_pred_all_rec_aux
  (D : Type)
  (I : Interpretation_ D)
  (V V' : Valuation_ D)
  (E : Env_)
  (τ : PredName_ → ℕ → List VarName_ × Formula_)
  (binders : Finset VarName_)
  (F : Formula_)
  (h1 : admits_pred_all_rec_aux τ binders F)
  (h2 : ∀ x : VarName_, x ∉ binders → V x = V' x) :
  holds D
    ⟨
      I.nonempty,
      I.pred_const_,
      fun (X : PredName_) (ds : List D) =>
        if ds.length = (τ X ds.length).fst.length
        then holds D I (Function.updateFromPairOfListsITE V' (τ X ds.length).fst ds) E (τ X ds.length).snd
        else I.pred_var_ X ds
      ⟩
      V E F ↔ holds D I V E (replace_pred_all_rec τ F) :=
  by
  induction F generalizing binders V
  case pred_const_ X xs =>
    simp only [replace_pred_all_rec]
    simp only [holds]
  case pred_var_ X xs =>
    simp only [admits_pred_all_rec_aux] at h1
    obtain ⟨h1_left, ⟨h1_right_left, h1_right_right⟩⟩ := h1

    obtain s1 :=
    Sub.Var.All.Rec.substitution_theorem_admits_var_all_rec D I V E (Function.updateFromPairOfListsITE id (τ X xs.length).fst xs)
      (τ X xs.length).snd h1_left
    simp only [Function.updateFromPairOfListsITE_comp] at s1
    simp only [CompTriple.comp_eq] at s1

    have s2 :
      holds D I (Function.updateFromPairOfListsITE V (τ X xs.length).fst (List.map V xs)) E (τ X xs.length).snd ↔
      holds D I (Function.updateFromPairOfListsITE V' (τ X xs.length).fst (List.map V xs)) E (τ X xs.length).snd :=
    by
      apply holds_coincide_var
      intro v a1
      by_cases c1 : v ∈ (τ X xs.length).fst
      · apply Function.updateFromPairOfListsITE_mem_eq_len V V' v (τ X xs.length).fst (List.map V xs) c1
        simp only [List.length_map]
        rewrite [← h1_right_right]
        apply Eq.refl
      · by_cases c2 : v ∈ binders
        · exfalso
          apply h1_right_left v c2
          exact ⟨a1, c1⟩
        · apply Function.updateFromPairOfListsITE_mem'
          exact h2 v c2

    simp only [s2] at s1

    simp only [holds]
    simp only [replace_pred_all_rec]
    simp only [List.length_map]
    split
    case isTrue c1 =>
      exact s1
    case isFalse c1 =>
      contradiction
  case eq_ x y =>
    simp only [replace_pred_all_rec]
    simp only [holds]
  case true_ | false_ =>
    simp only [replace_pred_all_rec]
    simp only [holds]
  case not_ phi phi_ih =>
    simp only [admits_pred_all_rec_aux] at h1

    simp only [replace_pred_all_rec]
    simp only [holds]
    congr! 1
    exact phi_ih V binders h1 h2
  case
      imp_ phi psi phi_ih psi_ih
    | and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    simp only [admits_pred_all_rec_aux] at h1
    obtain ⟨h1_left, h1_right⟩ := h1

    simp only [replace_pred_all_rec]
    simp only [holds]
    congr! 1
    · exact phi_ih V binders h1_left h2
    · exact psi_ih V binders h1_right h2
  case forall_ x phi phi_ih | exists_ x phi phi_ih =>
    simp only [admits_pred_all_rec_aux] at h1

    simp only [replace_pred_all_rec]
    simp only [holds]

    first | apply forall_congr' | apply exists_congr
    intro d

    apply phi_ih (Function.updateITE V x d) (binders ∪ {x}) h1
    intro v a1
    simp only [Finset.union_singleton, Finset.mem_insert] at a1
    rewrite [not_or] at a1
    obtain ⟨a1_left, a1_right⟩ := a1

    simp only [Function.updateITE]
    split
    case isTrue c1 =>
      contradiction
    case isFalse c1 =>
      apply h2
      exact a1_right
  case def_ X xs =>
    cases E
    case nil =>
      simp only [replace_pred_all_rec]
      simp only [holds]
    case cons hd tl =>
      simp only [replace_pred_all_rec]
      simp only [holds]
      split
      case isTrue c1 =>
        apply holds_coincide_pred_var
        · simp only
        · simp only [pred_var_occurs_in_iff_mem_pred_var_set]
          simp only [hd.h2]
          intro P ds a1
          simp only [Finset.notMem_empty] at a1
      case isFalse c1 =>
        apply holds_coincide_pred_var
        · simp only
        · simp only [pred_var_occurs_in]
          intro P ds a1
          contradiction


theorem substitution_theorem_admits_pred_all_rec
  (D : Type)
  (I : Interpretation_ D)
  (V : Valuation_ D)
  (E : Env_)
  (τ : PredName_ → ℕ → List VarName_ × Formula_)
  (F : Formula_)
  (h1 : admits_pred_all_rec τ F) :
  holds D
    ⟨
      I.nonempty,
      I.pred_const_,
      fun (X : PredName_) (ds : List D) =>
        let zs := (τ X ds.length).fst
        let H := (τ X ds.length).snd
        if ds.length = zs.length
        then holds D I (Function.updateFromPairOfListsITE V zs ds) E H
        else I.pred_var_ X ds
      ⟩
      V E F ↔ holds D I V E (replace_pred_all_rec τ F) :=
  by
  apply substitution_theorem_admits_pred_all_rec_aux D I V V E τ ∅ F
  · simp only [admits_pred_all_rec] at h1
    exact h1
  · intro X a1
    apply Eq.refl


theorem substitution_is_valid_admits_pred_all_rec
  (F : Formula_)
  (τ : PredName_ → ℕ → List VarName_ × Formula_)
  (h1 : admits_pred_all_rec τ F)
  (h2 : F.is_valid) :
  (replace_pred_all_rec τ F).is_valid :=
  by
  simp only [is_valid] at h2

  simp only [is_valid]
  intro D I V E
  obtain s1 := substitution_theorem_admits_pred_all_rec D I V E τ F h1
  simp only [← s1]
  apply h2


end FOL.NV.Sub.Pred.All.Rec


--#lint
