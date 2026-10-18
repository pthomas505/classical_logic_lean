import MathlibExtraLean.Finset
import MathlibExtraLean.FunctionUpdateITE
import ClassicalLogicLean.NV.Formula
import ClassicalLogicLean.NV.Fresh
import ClassicalLogicLean.NV.Semantics
import ClassicalLogicLean.NV.Sub.Var.All.Rec.Admits


set_option linter.style.docString false
set_option linter.style.emptyLine false
set_option linter.style.longLine false


namespace FOL.NV.Sub.Var.All.Rec.Fresh

open Formula_


/--
  `sub_var_all_rec σ c F` := The simultaneous replacement of each free occurrence of any variable `v` in the formula `F` by `σ v`. The character `c` is used to generate fresh binding variables as needed to avoid free variable capture.
-/
@[nolint defsWithUnderscore]
def sub_var_all_rec
  (σ : VarName_ → VarName_)
  (c : Char) :
  Formula_ → Formula_
  | pred_const_ X xs => pred_const_ X (xs.map σ)
  | pred_var_ X xs => pred_var_ X (xs.map σ)
  | eq_ x y => eq_ (σ x) (σ y)
  | true_ => true_
  | false_ => false_
  | not_ phi => not_ (sub_var_all_rec σ c phi)
  | imp_ phi psi => imp_ (sub_var_all_rec σ c phi) (sub_var_all_rec σ c psi)
  | and_ phi psi => and_ (sub_var_all_rec σ c phi) (sub_var_all_rec σ c psi)
  | or_ phi psi => or_ (sub_var_all_rec σ c phi) (sub_var_all_rec σ c psi)
  | iff_ phi psi => iff_ (sub_var_all_rec σ c phi) (sub_var_all_rec σ c psi)
  | forall_ x phi =>
    let x' : VarName_ :=
      if ∃ (y : VarName_), y ∈ phi.free_var_set \ {x} ∧ σ y = x
      then fresh x c ((sub_var_all_rec (Function.updateITE σ x x) c phi).free_var_set)
      else x
    forall_ x' (sub_var_all_rec (Function.updateITE σ x x') c phi)
  | exists_ x phi =>
    let x' : VarName_ :=
      if ∃ (y : VarName_), y ∈ phi.free_var_set \ {x} ∧ σ y = x
      then fresh x c ((sub_var_all_rec (Function.updateITE σ x x) c phi).free_var_set)
      else x
    exists_ x' (sub_var_all_rec (Function.updateITE σ x x') c phi)
  | def_ X xs => def_ X (xs.map σ)


theorem sub_var_all_rec_free_var_set_eq_free_var_set_image
  (σ : VarName_ → VarName_)
  (c : Char)
  (F : Formula_) :
  (sub_var_all_rec σ c F).free_var_set = F.free_var_set.image σ :=
  by
  induction F generalizing σ
  all_goals
    simp only [sub_var_all_rec]
    simp only [free_var_set]
  case pred_const_ X xs | pred_var_ X xs | def_ X xs =>
    ext x
    simp only [List.mem_toFinset, List.mem_map, Finset.mem_image]
  case eq_ x y =>
    simp only [Finset.image_insert, Finset.image_singleton]
  case true_ | false_ =>
    simp only [Finset.image_empty]
  case not_ phi phi_ih =>
    apply phi_ih
  case
      imp_ phi psi phi_ih psi_ih
    | and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    simp only [Finset.image_union]
    congr!
    · apply phi_ih
    · apply psi_ih
  case forall_ x phi phi_ih | exists_ x phi phi_ih =>
    simp only [phi_ih]

    simp only [<- Finset.image_sdiff_singleton_updateITE phi.free_var_set x x σ]

    split
    case isTrue c1 =>
      obtain s1 := fresh_not_mem x c (Finset.image (Function.updateITE σ x x) (free_var_set phi))

      generalize ( fresh x c (Finset.image (Function.updateITE σ x x) (free_var_set phi)) ) = x' at *

      have s2 : Finset.image (Function.updateITE σ x x) (free_var_set phi \ {x}) ⊆ Finset.image (Function.updateITE σ x x) (free_var_set phi) :=
      by
        apply Finset.image_subset_image
        simp only [Finset.sdiff_subset]

      have s3 : x' ∉ Finset.image (Function.updateITE σ x x) (free_var_set phi \ {x}) :=
      by
        exact Finset.notMem_mono s2 s1

      calc
        Finset.image (Function.updateITE σ x x') (free_var_set phi) \ {x'}
      = Finset.image (Function.updateITE σ x x') (free_var_set phi \ {x}) \ {x'} :=
        by
          apply Finset.image_sdiff_singleton phi.free_var_set x x' (Function.updateITE σ x x')
          simp only [Function.updateITE]
          split
          case isTrue c2 =>
            apply Eq.refl
          case isFalse c2 =>
            exfalso
            apply c2
            exact True.intro
      _ = Finset.image (Function.updateITE σ x x) (free_var_set phi \ {x}) \ {x'} :=
          by simp only [Finset.image_congr_update_ite phi.free_var_set x x' x]
      _ = Finset.image (Function.updateITE σ x x) (free_var_set phi \ {x}) :=
          by
            simp only [Finset.sdiff_singleton_eq_erase] at s3
            simp only [Finset.sdiff_singleton_eq_erase]
            exact Finset.erase_eq_of_notMem s3
    case isFalse c1 =>
      simp only [Finset.mem_sdiff, Finset.mem_singleton, not_exists] at c1

      have s1 : Finset.image (Function.updateITE σ x x) (free_var_set phi) \ {x} = Finset.image (Function.updateITE σ x x) (free_var_set phi \ {x}) \ {x} :=
      by
        apply Finset.image_sdiff_singleton
        simp only [Function.updateITE]
        split
        case isTrue c2 =>
          apply Eq.refl
        case isFalse c2 =>
          exfalso
          apply c2
          exact True.intro
      rewrite [s1]

      have s2 : x ∉ Finset.image (Function.updateITE σ x x) (free_var_set phi \ {x}) :=
      by
        simp only [Finset.mem_image]
        simp only [Finset.mem_sdiff, Finset.mem_singleton, not_exists]
        simp only [Function.updateITE]
        intro v a1
        obtain ⟨⟨a1_left_left, a1_left_right⟩, a1_right⟩ := a1
        split at a1_right
        case isTrue c2 =>
          contradiction
        case isFalse c2 =>
          apply c1 v
          exact ⟨⟨a1_left_left, a1_left_right⟩, a1_right⟩

      simp only [Finset.sdiff_singleton_eq_erase] at s2

      simp only [Finset.sdiff_singleton_eq_erase]
      exact Finset.erase_eq_of_notMem s2


theorem substitution_theorem_sub_var_all_rec
  (D : Type)
  (I : Interpretation_ D)
  (V : Valuation_ D)
  (E : Env_)
  (σ : VarName_ → VarName_)
  (c : Char)
  (F : Formula_) :
  holds D I V E (sub_var_all_rec σ c F) ↔
    holds D I (V ∘ σ) E F :=
  by
  induction F generalizing σ V
  case pred_const_ X xs | pred_var_ X xs =>
    simp only [sub_var_all_rec]
    simp only [holds]
    simp only [List.map_map]
  case eq_ x y =>
    simp only [sub_var_all_rec]
    simp only [holds]
    simp only [Function.comp_apply]
  case true_ | false_ =>
    simp only [sub_var_all_rec]
    simp only [holds]
  case not_ phi phi_ih =>
    simp only [sub_var_all_rec]
    simp only [holds]
    congr! 1
    apply phi_ih
  case
      imp_ phi psi phi_ih psi_ih
    | and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    simp only [sub_var_all_rec]
    simp only [holds]
    congr! 1
    · apply phi_ih
    · apply psi_ih
  case forall_ x phi phi_ih | exists_ x phi phi_ih =>
    simp only [sub_var_all_rec]
    simp only [holds]

    first | apply forall_congr' | apply exists_congr
    intro d

    simp only [phi_ih]
    apply holds_coincide_var
    intro v a1

    simp only [Finset.mem_sdiff, Finset.mem_singleton, Function.comp_apply]
    split
    case isTrue c1 =>
      obtain s1 := fresh_not_mem x c (free_var_set (sub_var_all_rec (Function.updateITE σ x x) c phi))

      generalize (fresh x c (free_var_set (sub_var_all_rec (Function.updateITE σ x x) c phi))) = x' at *
      by_cases c2 : v = x
      · simp only [c2]
        simp only [Function.updateITE]
        split
        case isTrue c3 =>
          split
          case isTrue c4 =>
            apply Eq.refl
          case isFalse c4 =>
            contradiction
        case isFalse c3 =>
          exfalso
          apply c3
          exact True.intro
      · by_cases c3 : σ v = x'
        · rewrite [← c3] at s1
          simp only [sub_var_all_rec_free_var_set_eq_free_var_set_image] at s1

          have s2 : σ v ∈ Finset.image (Function.updateITE σ x x) (free_var_set phi) :=
          by
            apply Finset.mem_image_update
            · exact c2
            · simp only [← var_is_free_in_iff_mem_free_var_set]
              exact a1

          contradiction
        · simp only [Function.updateITE]
          split
          case isTrue c4 =>
            contradiction
          case isFalse c4 =>
            simp only [Function.comp_apply]

    case isFalse c1 =>
      by_cases c2 : v = x
      · rewrite [c2]
        simp only [Function.updateITE]
        split
        case isTrue c3 =>
          split
          case isTrue c4 =>
            apply Eq.refl
          case isFalse c4 =>
            contradiction
        case isFalse c3 =>
          exfalso
          apply c3
          exact True.intro
      · have s1 : ¬ σ v = x :=
        by
          intro contra
          apply c1
          apply Exists.intro v
          constructor
          · simp only [Finset.mem_sdiff, Finset.mem_singleton]
            simp only [← var_is_free_in_iff_mem_free_var_set]
            exact ⟨a1, c2⟩
          · exact contra

        simp only [Function.updateITE]
        split
        case isTrue c3 =>
          contradiction
        case isFalse c3 =>
          simp only [Function.comp_apply]
  case def_ X xs =>
    induction E
    case nil =>
      simp only [sub_var_all_rec]
      simp only [holds]
    case cons E_hd E_tl E_ih =>
      simp only [sub_var_all_rec] at E_ih

      simp only [sub_var_all_rec]
      simp only [holds]
      simp only [List.length_map, List.map_map]
      split
      case isTrue c1 =>
        apply holds_coincide_var
        intro v a1
        apply Function.updateFromPairOfListsITE_map_mem_ext
        · intro y a2
          apply Eq.refl
        · obtain ⟨c1_left, c1_right⟩ := c1
          rewrite [c1_right]
          apply Eq.refl
        · simp only [var_is_free_in_iff_mem_free_var_set] at a1
          simp only [← List.mem_toFinset]
          exact Finset.mem_of_subset E_hd.h1 a1
      case isFalse c1 =>
        exact E_ih


theorem substitution_is_valid_sub_var_all_rec
  (σ : VarName_ → VarName_)
  (c : Char)
  (F : Formula_)
  (h1 : is_valid F) :
  is_valid (sub_var_all_rec σ c F) :=
  by
  simp only [is_valid] at h1

  simp only [is_valid]
  intro D I V E
  simp only [substitution_theorem_sub_var_all_rec]
  apply h1

-------------------------------------------------------------------------------

theorem sub_var_all_rec_id
  (c : Char)
  (F : Formula_) :
  sub_var_all_rec id c F = F :=
  by
  induction F
  case pred_const_ X xs | pred_var_ X xs | def_ X xs =>
    simp only [sub_var_all_rec]
    simp only [List.map_id_fun, id_eq]
  case eq_ x y =>
    simp only [sub_var_all_rec]
    simp only [id_eq]
  case true_ | false_ =>
    simp only [sub_var_all_rec]
  case not_ phi phi_ih =>
    simp only [sub_var_all_rec]
    congr!
  case
      imp_ phi psi phi_ih psi_ih
    | and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    simp only [sub_var_all_rec]
    congr!
  case forall_ x phi phi_ih | exists_ x phi phi_ih =>
    simp only [sub_var_all_rec]
    simp only [Function.updateITE_id]
    congr
    · split
      case isTrue c1 =>
        obtain ⟨y, ⟨c1_left, c1_right⟩⟩ := c1
        simp only [Finset.mem_sdiff, Finset.mem_singleton] at c1_left
        obtain ⟨c1_left_left, c1_left_right⟩ := c1_left
        simp only [id_eq] at c1_right
        contradiction
      case isFalse c1 =>
        apply Eq.refl
    · split
      case isTrue c1 =>
        obtain ⟨y, ⟨c1_left, c1_right⟩⟩ := c1
        simp only [Finset.mem_sdiff, Finset.mem_singleton] at c1_left
        obtain ⟨c1_left_left, c1_left_right⟩ := c1_left
        simp only [id_eq] at c1_right
        contradiction
      case isFalse c1 =>
        simp only [Function.updateITE_id]
        exact phi_ih


example
  (σ : VarName_ → VarName_)
  (c : Char)
  (F : Formula_)
  (h1 : FOL.NV.Sub.Var.All.Rec.admits_var_all_rec σ F) :
  sub_var_all_rec σ c F = FOL.NV.Sub.Var.All.Rec.fast_replace_free_var_all_rec σ F :=
  by
  induction F generalizing σ
  case
      pred_const_ X xs
    | pred_var_ X xs
    | eq_ x y
    | true_
    | false_
    | def_ X xs =>
    simp only [sub_var_all_rec]
    simp only [fast_replace_free_var_all_rec]
  case not_ phi ih =>
    simp only [admits_var_all_rec] at ih

    simp only [admits_var_all_rec] at h1
    simp only [admits_var_all_rec_aux] at h1

    simp only [sub_var_all_rec]
    simp only [fast_replace_free_var_all_rec]
    congr
    apply ih
    exact h1
  case
      imp_ phi psi phi_ih psi_ih
    | and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    simp only [admits_var_all_rec] at phi_ih
    simp only [admits_var_all_rec] at psi_ih

    simp only [admits_var_all_rec] at h1
    simp only [admits_var_all_rec_aux] at h1

    simp only [sub_var_all_rec]
    simp only [fast_replace_free_var_all_rec]
    congr
    · tauto
    · tauto
  case
      forall_ x phi ih
    | exists_ x phi ih =>
    simp only [admits_var_all_rec] at ih

    simp only [admits_var_all_rec] at h1
    simp only [admits_var_all_rec_aux] at h1
    simp only [Finset.empty_union] at h1

    simp only [sub_var_all_rec]
    simp only [fast_replace_free_var_all_rec]

    have s1 : ¬ ∃ y ∈ phi.free_var_set \ {x}, σ y = x :=
    by
      simp only [Finset.mem_sdiff, Finset.mem_singleton, not_exists]
      intro v a1
      obtain ⟨⟨a1_left_left, a1_left_right⟩, a1_right⟩ := a1
      apply admits_var_all_rec_aux_mem_free_var_set_and_not_mem_binders {x} σ phi h1 v
      · exact a1_left_left
      · simp only [Finset.mem_singleton]
        exact a1_left_right
      · simp only [Finset.mem_singleton]
        exact a1_right

    congr
    · split
      case isTrue c1 =>
        contradiction
      case isFalse c1 =>
        apply Eq.refl
    · split
      case isTrue c1 =>
        contradiction
      case isFalse c1 =>
        apply ih
        apply admits_var_all_rec_aux_del_binder
        simp only [Finset.union_empty]
        exact h1


end FOL.NV.Sub.Var.All.Rec.Fresh


#lint
