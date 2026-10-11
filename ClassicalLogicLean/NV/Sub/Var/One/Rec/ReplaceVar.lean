import MathlibExtraLean.List
import ClassicalLogicLean.NV.Binders


set_option linter.style.docString false
set_option linter.style.emptyLine false
set_option linter.style.longLine false


open Formula_


/--
  `replace_var_one_rec v t P` :=

  `v → t` in `P` for each occurrence of `v` in `P`

  The result of replacing each occurrence of `v` in `P` by an occurrence of `t`.
-/
@[nolint defsWithUnderscore]
def replace_var_one_rec (v t : VarName_) : Formula_ → Formula_
  | pred_const_ X xs =>
      pred_const_
      X
      (xs.map fun (x : VarName_) => if v = x then t else x)
  | pred_var_ X xs =>
      pred_var_
      X
      (xs.map fun (x : VarName_) => if v = x then t else x)
  | eq_ x y =>
      eq_
      (if v = x then t else x)
      (if v = y then t else y)
  | true_ => true_
  | false_ => false_
  | not_ phi => not_ (replace_var_one_rec v t phi)
  | imp_ phi psi => imp_ (replace_var_one_rec v t phi) (replace_var_one_rec v t psi)
  | and_ phi psi => and_ (replace_var_one_rec v t phi) (replace_var_one_rec v t psi)
  | or_ phi psi => or_ (replace_var_one_rec v t phi) (replace_var_one_rec v t psi)
  | iff_ phi psi => iff_ (replace_var_one_rec v t phi) (replace_var_one_rec v t psi)
  | forall_ x phi =>
      if v = x
      then forall_ t (replace_var_one_rec v t phi)
      else forall_ x (replace_var_one_rec v t phi)
  | exists_ x phi =>
      if v = x
      then exists_ t (replace_var_one_rec v t phi)
      else exists_ x (replace_var_one_rec v t phi)
  | def_ X xs =>
      def_
      X
      (xs.map fun (x : VarName_) => if v = x then t else x)


theorem replace_var_one_rec_self
  (F : Formula_)
  (v : VarName_) :
  replace_var_one_rec v v F = F :=
  by
  induction F
  any_goals
    simp only [replace_var_one_rec]
  case pred_const_ X xs | pred_var_ X xs | def_ X xs =>
    congr
    simp only [List.map_eq_self_iff_fun_is_id_on_mem]
    intro x a1
    split
    case isTrue c1 =>
      exact c1
    case isFalse c1 =>
      apply Eq.refl
  case eq_ x y =>
    congr
    all_goals
      split
      case isTrue c1 =>
        exact c1
      case isFalse c1 =>
        apply Eq.refl
  case not_ phi phi_ih =>
    rewrite [phi_ih]
    apply Eq.refl
  case
      imp_ phi psi phi_ih psi_ih
    | and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    rewrite [phi_ih]
    rewrite [psi_ih]
    apply Eq.refl
  case forall_ x phi phi_ih | exists_ x phi phi_ih =>
    split
    case isTrue c1 =>
      rewrite [phi_ih]
      rewrite [c1]
      apply Eq.refl
    case isFalse c1 =>
      rewrite [phi_ih]
      apply Eq.refl


theorem not_var_occurs_in_replace_var_one_rec_self
  (F : Formula_)
  (v t : VarName_)
  (h1 : ¬ var_occurs_in v F) :
  replace_var_one_rec v t F = F :=
  by
  induction F
  any_goals
    simp only [var_occurs_in] at h1

    simp only [replace_var_one_rec]
  case pred_const_ X xs | pred_var_ X xs | def_ X xs =>
    congr
    simp only [List.map_eq_self_iff_fun_is_id_on_mem]
    intro x a1
    split
    case isTrue c1 =>
      rewrite [c1] at h1
      contradiction
    case isFalse c1 =>
      apply Eq.refl
  case eq_ x y =>
    rewrite [not_or] at h1
    obtain ⟨h1_left, h1_right⟩ := h1

    congr
    all_goals
      split
      case isTrue c1 =>
        contradiction
      case isFalse c1 =>
        apply Eq.refl
  case not_ phi phi_ih =>
    congr
    exact phi_ih h1
  case
      imp_ phi psi phi_ih psi_ih
    | and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    rewrite [not_or] at h1
    obtain ⟨h1_left, h1_right⟩ := h1

    congr
    · exact phi_ih h1_left
    · exact psi_ih h1_right
  case forall_ x phi phi_ih | exists_ x phi phi_ih =>
    rewrite [not_or] at h1
    obtain ⟨h1_left, h1_right⟩ := h1

    split
    case isTrue c1 =>
      contradiction
    case isFalse c1 =>
      congr
      exact phi_ih h1_right


theorem replace_var_one_rec_inverse
  (F : Formula_)
  (v t : VarName_)
  (h1 : ¬ var_occurs_in t F) :
  replace_var_one_rec t v (replace_var_one_rec v t F) = F :=
  by
  induction F
  any_goals
    simp only [var_occurs_in] at h1

    simp only [replace_var_one_rec]
  case pred_const_ X xs | pred_var_ X xs | def_ X xs =>
    congr
    simp only [List.map_map]
    simp only [List.map_eq_self_iff_fun_is_id_on_mem]
    simp only [Function.comp_apply]
    intro x a1
    split
    case isTrue c1 =>
      split
      case isTrue c2 =>
        exact c1
      case isFalse c2 =>
        contradiction
    case isFalse c1 =>
      split
      case isTrue c2 =>
        rewrite [c2] at h1
        contradiction
      case isFalse c2 =>
        apply Eq.refl
  case eq_ x y =>
    rewrite [not_or] at h1
    obtain ⟨h1_left, h1_right⟩ := h1

    congr
    all_goals
      split
      case isTrue c1 =>
        split
        case isTrue c2 =>
          exact c1
        case isFalse c2 =>
          contradiction
      case isFalse c1 =>
        apply Eq.refl
  case not_ phi phi_ih =>
    congr
    exact phi_ih h1
  case
      imp_ phi psi phi_ih psi_ih
    | and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    rewrite [not_or] at h1
    obtain ⟨h1_left, h1_right⟩ := h1

    congr
    · exact phi_ih h1_left
    · exact psi_ih h1_right
  case forall_ x phi phi_ih | exists_ x phi phi_ih =>
    rewrite [not_or] at h1
    obtain ⟨h1_left, h1_right⟩ := h1

    split
    case isTrue c1 =>
      simp only [replace_var_one_rec]
      split
      case isTrue c2 =>
        congr
        exact phi_ih h1_right
      case isFalse c2 =>
        contradiction
    case isFalse c1 =>
      simp only [replace_var_one_rec]
      split
      case isTrue c2 =>
        contradiction
      case isFalse c2 =>
        congr
        exact phi_ih h1_right


theorem not_var_occurs_in_replace_var_one_rec
  (F : Formula_)
  (v t : VarName_)
  (h1 : ¬ v = t) :
  ¬ var_occurs_in v (replace_var_one_rec v t F) :=
  by
  induction F
  any_goals
    simp only [replace_var_one_rec]
    simp only [var_occurs_in]
  case pred_const_ X xs | pred_var_ X xs | def_ X xs =>
    simp only [List.mem_map, not_exists]
    intro x a1
    obtain ⟨a1_left, a1_right⟩ := a1
    split at a1_right
    case isTrue c1 =>
      rewrite [a1_right] at h1
      contradiction
    case isFalse c1 =>
      rewrite [a1_right] at c1
      contradiction
  case eq_ x y =>
    rewrite [not_or]
    constructor
    all_goals
      split
      case isTrue c1 =>
        exact h1
      case isFalse c1 =>
        exact c1
  case true_ | false_ =>
    intro contra
    exact contra
  case not_ phi phi_ih =>
    exact phi_ih
  case
      imp_ phi psi phi_ih psi_ih
    | and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    rewrite [not_or]
    constructor
    · exact phi_ih
    · exact psi_ih
  case forall_ x phi phi_ih | exists_ x phi phi_ih =>
    simp only [replace_var_one_rec]
    split
    case isTrue c1 =>
      simp only [var_occurs_in]
      rewrite [not_or]
      exact ⟨h1, phi_ih⟩
    case isFalse c1 =>
      simp only [var_occurs_in]
      rewrite [not_or]
      exact ⟨c1, phi_ih⟩


theorem replace_var_one_rec_free_var_set_sdiff
  (F : Formula_)
  (v t : VarName_)
  (h1 : t ∉ F.var_set) :
  F.free_var_set \ {v} = (replace_var_one_rec v t F).free_var_set \ {t} :=
  by
    induction F
    all_goals
      simp only [var_set] at h1
    case pred_const_ X xs | pred_var_ X xs | def_ X xs =>
      simp only [replace_var_one_rec]
      simp only [free_var_set]
      ext x
      simp only [Finset.mem_sdiff, List.mem_toFinset, Finset.mem_singleton, List.mem_map]
      constructor
      · intro a1
        obtain ⟨a1_left, a1_right⟩ := a1
        constructor
        · apply Exists.intro x
          simp only [Eq.comm] at a1_right
          split
          case isTrue c1 =>
            contradiction
          case isFalse c1 =>
            exact ⟨a1_left, rfl⟩
        · intro contra
          apply h1
          rewrite [← contra]
          simp only [List.mem_toFinset]
          exact a1_left
      · intro a1
        obtain ⟨⟨y, ⟨a1_left_left, a1_left_right⟩⟩, a1_right⟩ := a1
        split at a1_left_right
        case isTrue c1 =>
          rewrite [a1_left_right] at a1_right
          contradiction
        case isFalse c1 =>
          rewrite [← a1_left_right]
          constructor
          · exact a1_left_left
          · intro contra
            apply c1
            rewrite [contra]
            apply Eq.refl
    case eq_ x y =>
      simp only [Finset.mem_insert, Finset.mem_singleton] at h1
      rewrite [not_or] at h1
      obtain ⟨h1_left, h1_right⟩ := h1

      simp only [replace_var_one_rec]
      simp only [free_var_set]
      simp only [Finset.sdiff_singleton_eq_erase]
      split
      case isTrue c1 =>
        split
        case isTrue c2 =>
          rewrite [← c1]
          rewrite [← c2]
          simp only [Finset.mem_singleton, Finset.insert_eq_of_mem, Finset.erase_singleton]
        case isFalse c2 =>
          rewrite [← c1]
          simp only [Finset.erase_insert_eq_erase]

          simp only [← Finset.mem_singleton] at c2
          obtain s1 := Finset.erase_eq_of_notMem c2
          rewrite [s1]

          simp only [← Finset.mem_singleton] at h1_right
          obtain s2 := Finset.erase_eq_of_notMem h1_right
          rewrite [s2]

          apply Eq.refl
      case isFalse c1 =>
        split
        case isTrue c2 =>
          simp only [Finset.pair_comm x y]
          simp only [Finset.pair_comm x t]

          rewrite [c2]
          simp only [Finset.erase_insert_eq_erase]
          rewrite [← c2]

          simp only [← Finset.mem_singleton] at c1
          obtain s1 := Finset.erase_eq_of_notMem c1
          rewrite [s1]

          simp only [← Finset.mem_singleton] at h1_left
          obtain s2 := Finset.erase_eq_of_notMem h1_left
          rewrite [s2]

          apply Eq.refl
        case isFalse c2 =>
          have s1 : v ∉ ({x, y} : Finset VarName_) :=
          by
            simp only [Finset.mem_insert, Finset.mem_singleton]
            rewrite [not_or]
            exact ⟨c1, c2⟩
          obtain s2 := Finset.erase_eq_of_notMem s1
          rewrite [s2]

          have s3 : t ∉ ({x, y} : Finset VarName_) :=
          by
            simp only [Finset.mem_insert, Finset.mem_singleton]
            rewrite [not_or]
            exact ⟨h1_left, h1_right⟩
          obtain s4 := Finset.erase_eq_of_notMem s3
          rewrite [s4]

          apply Eq.refl
    case true_ | false_ =>
      simp only [replace_var_one_rec]
      simp only [free_var_set]
      simp only [Finset.empty_sdiff]
    case not_ phi phi_ih =>
      simp only [replace_var_one_rec]
      simp only [free_var_set]
      exact phi_ih h1
    case
        imp_ phi psi phi_ih psi_ih
      | and_ phi psi phi_ih psi_ih
      | or_ phi psi phi_ih psi_ih
      | iff_ phi psi phi_ih psi_ih =>
      simp only [Finset.mem_union] at h1
      rewrite [not_or] at h1
      obtain ⟨h1_left, h1_right⟩ := h1

      simp only [replace_var_one_rec]
      simp only [free_var_set]
      simp only [Finset.union_sdiff_distrib]
      rewrite [phi_ih h1_left]
      rewrite [psi_ih h1_right]
      apply Eq.refl
    case forall_ x phi phi_ih | exists_ x phi phi_ih =>
      simp only [Finset.union_singleton, Finset.mem_insert] at h1
      rewrite [not_or] at h1
      obtain ⟨h1_left, h1_right⟩ := h1

      simp only [replace_var_one_rec]
      split
      case isTrue c1 =>
        rewrite [← c1]
        simp only [free_var_set]
        simp only [sdiff_idem]
        exact phi_ih h1_right
      case isFalse c1 =>
        simp only [free_var_set]
        simp only [sdiff_sdiff_comm]
        congr 1
        exact phi_ih h1_right


#lint
