import ClassicalLogicLean.NV.Sub.Pred.All.Rec.Option.Replace
import ClassicalLogicLean.NV.Sub.Var.All.Rec.Sub


set_option linter.style.docString false
set_option linter.style.emptyLine false
set_option linter.style.longLine false


namespace FOL.NV.Sub.Pred.All.Rec.Option

open Formula_


def admits_pred_all_rec_opt_aux
  (τ : PredName_ → ℕ → Option (List VarName_ × Formula_))
  (binders : Finset VarName_) : Formula_ → Prop
  | pred_const_ _ _ => True
  | pred_var_ X xs =>
      let opt := τ X xs.length
      if h : Option.isSome opt
      then
        let val := Option.get opt h
        let zs := val.fst
        let H := val.snd
        if xs.length = zs.length
        then binders ∩ (H.free_var_set \ zs.toFinset) = ∅
        --then ∀ x : VarName_, x ∈ binders → ¬ (var_is_free_in x H ∧ x ∉ zs)
        else True
      else True
  | true_ => True
  | false_ => True
  | eq_ _ _ => True
  | not_ phi => admits_pred_all_rec_opt_aux τ binders phi
  | imp_ phi psi =>
      admits_pred_all_rec_opt_aux τ binders phi ∧
      admits_pred_all_rec_opt_aux τ binders psi
  | and_ phi psi =>
      admits_pred_all_rec_opt_aux τ binders phi ∧
      admits_pred_all_rec_opt_aux τ binders psi
  | or_ phi psi =>
      admits_pred_all_rec_opt_aux τ binders phi ∧
      admits_pred_all_rec_opt_aux τ binders psi
  | iff_ phi psi =>
      admits_pred_all_rec_opt_aux τ binders phi ∧
      admits_pred_all_rec_opt_aux τ binders psi
  | forall_ x phi => admits_pred_all_rec_opt_aux τ (binders ∪ {x}) phi
  | exists_ x phi => admits_pred_all_rec_opt_aux τ (binders ∪ {x}) phi
  | def_ _ _ => True


theorem substitution_theorem_admits_pred_all_rec_opt_aux
  (D : Type)
  (I : Interpretation_ D)
  (V V' : Valuation_ D)
  (E : Env_)
  (c : Char)
  (τ : PredName_ → ℕ → Option (List VarName_ × Formula_))
  (binders : Finset VarName_)
  (F : Formula_)
  (h1 : admits_pred_all_rec_opt_aux τ binders F)
  (h2 : ∀ x : VarName_, x ∉ binders → V' x = V x) :
  holds D
    ⟨
      I.nonempty,
      I.pred_const_,
      fun (X : PredName_) (ds : List D) =>
      let opt := τ X ds.length
      if h : Option.isSome opt
      then
        let val := Option.get opt h
        let zs := val.fst
        let H := val.snd
        if ds.length = zs.length
        then holds D I (Function.updateFromPairOfListsITE V' zs ds) E H
        else I.pred_var_ X ds
      else I.pred_var_ X ds
    ⟩
    V E F ↔ holds D I V E (replace_pred_all_rec_opt c τ F) :=
  by
  induction F generalizing binders V
  case pred_const_ X xs =>
    simp only [replace_pred_all_rec_opt]
    simp only [holds]
  case pred_var_ X xs =>
    simp only [replace_pred_all_rec_opt]
    simp only [holds]
    simp only [List.length_map]

    simp only [admits_pred_all_rec_opt_aux] at h1
    split at h1
    case isTrue c1 =>
      split at h1
      case isTrue c2 =>
        simp only [Finset.eq_empty_iff_forall_notMem] at h1
        simp only [Finset.mem_inter, Finset.mem_sdiff, List.mem_toFinset] at h1

        split
        case isTrue c3 =>
          obtain s1 := Sub.Var.All.Rec.Fresh.substitution_theorem_sub_var_all_rec D I V E (Function.updateFromPairOfListsITE id (Option.get (τ X xs.length) c1).fst xs) c (Option.get (τ X xs.length) c1).snd
          simp only [Function.updateFromPairOfListsITE_comp] at s1
          simp only [CompTriple.comp_eq] at s1
          rewrite [s1]

          apply holds_coincide_var
          intro v a1
          by_cases c4 : v ∈ (Option.get (τ X xs.length) c1).fst
          · apply Function.updateFromPairOfListsITE_mem_eq_len V' V v (Option.get (τ X xs.length) c1).fst (List.map V xs) c4
            simp only [List.length_map]
            simp only [← c2]
          · simp only [Function.updateFromPairOfListsITE_not_mem V v ((Option.get (τ X xs.length) c1).fst) (List.map V xs) c4]
            simp only [Function.updateFromPairOfListsITE_not_mem V' v (Option.get (τ X xs.length) c1).fst (List.map V xs) c4]
            apply h2
            intro contra
            simp only [var_is_free_in_iff_mem_free_var_set] at a1
            exfalso
            apply h1 v
            tauto
        case isFalse c3 =>
          contradiction
      case isFalse c2 =>
        split
        case isTrue c3 =>
          simp only [holds]
        case isFalse c3 =>
          contradiction
    case isFalse c1 =>
      split
      case isTrue c2 =>
        contradiction
      case isFalse c2 =>
        simp only [holds]
  case eq_ x y =>
    simp only [replace_pred_all_rec_opt]
    simp only [holds]
  case true_ | false_ =>
    simp only [replace_pred_all_rec_opt]
    simp only [holds]
  case not_ phi phi_ih =>
    simp only [admits_pred_all_rec_opt_aux] at h1

    simp only [replace_pred_all_rec_opt]
    simp only [holds]
    congr! 1
    exact phi_ih V binders h1 h2
  case
      imp_ phi psi phi_ih psi_ih
    | and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    simp only [admits_pred_all_rec_opt_aux] at h1
    obtain ⟨h1_left, h1_right⟩ := h1

    simp only [replace_pred_all_rec_opt]
    simp only [holds]

    congr! 1
    · exact phi_ih V binders h1_left h2
    · exact psi_ih V binders h1_right h2
  case forall_ x phi phi_ih | exists_ x phi phi_ih =>
    simp only [admits_pred_all_rec_opt_aux] at h1

    simp only [replace_pred_all_rec_opt]
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
      exact h2 v a1_right
  case def_ X xs =>
    cases E
    case nil =>
      simp only [replace_pred_all_rec_opt]
      simp only [holds]
    case cons hd tl =>
      simp only [replace_pred_all_rec_opt]
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


end FOL.NV.Sub.Pred.All.Rec.Option
