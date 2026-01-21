/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.Limits.Preserves.Ulift
public import Mathlib.CategoryTheory.Limits.Presheaf
public import Mathlib.CategoryTheory.Sites.Canonical
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.CategoryTheory.Sites.Closed
public import Mathlib.CategoryTheory.Sites.Coverage

/-!

# Subcanonical Grothendieck topologies

This file provides some API for the Yoneda embedding into the category of sheaves for a
subcanonical Grothendieck topology.
-/

@[expose] public section

universe v' v u

namespace CategoryTheory.GrothendieckTopology

open Opposite Functor

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) [Subcanonical J]

/--
The equivalence between natural transformations from the yoneda embedding (to the sheaf category)
and elements of `F.val.obj X`.
-/
def yonedaEquiv {X : C} {F : Sheaf J (Type v)} : (J.yoneda.obj X ⟶ F) ≃ F.val.obj (op X) :=
  (fullyFaithfulSheafToPresheaf _ _).homEquiv.trans CategoryTheory.yonedaEquiv

theorem yonedaEquiv_apply {X : C} {F : Sheaf J (Type v)} (f : J.yoneda.obj X ⟶ F) :
    yonedaEquiv J f = f.val.app (op X) (𝟙 X) :=
  rfl

@[simp]
theorem yonedaEquiv_symm_app_apply {X : C} {F : Sheaf J (Type v)} (x : F.val.obj (op X)) (Y : Cᵒᵖ)
    (f : Y.unop ⟶ X) : (J.yonedaEquiv.symm x).val.app Y f = F.val.map f.op x :=
  rfl

/-- See also `yonedaEquiv_naturality'` for a more general version. -/
lemma yonedaEquiv_naturality {X Y : C} {F : Sheaf J (Type v)} (f : J.yoneda.obj X ⟶ F)
    (g : Y ⟶ X) : F.val.map g.op (J.yonedaEquiv f) = J.yonedaEquiv (J.yoneda.map g ≫ f) := by
  simp [yonedaEquiv, CategoryTheory.yonedaEquiv_naturality]
  rfl

/--
Variant of `yonedaEquiv_naturality` with general `g`. This is technically strictly more general
than `yonedaEquiv_naturality`, but `yonedaEquiv_naturality` is sometimes preferable because it
can avoid the "motive is not type correct" error.
-/
lemma yonedaEquiv_naturality' {X Y : Cᵒᵖ} {F : Sheaf J (Type v)} (f : J.yoneda.obj (unop X) ⟶ F)
    (g : X ⟶ Y) : F.val.map g (J.yonedaEquiv f) = J.yonedaEquiv (J.yoneda.map g.unop ≫ f) :=
  J.yonedaEquiv_naturality _ _

lemma yonedaEquiv_comp {X : C} {F G : Sheaf J (Type v)} (α : J.yoneda.obj X ⟶ F) (β : F ⟶ G) :
    J.yonedaEquiv (α ≫ β) = β.val.app _ (J.yonedaEquiv α) :=
  rfl

lemma yonedaEquiv_yoneda_map {X Y : C} (f : X ⟶ Y) : J.yonedaEquiv (J.yoneda.map f) = f := by
  rw [yonedaEquiv_apply]
  simp

lemma yonedaEquiv_symm_naturality_left {X X' : C} (f : X' ⟶ X) (F : Sheaf J (Type v))
    (x : F.val.obj ⟨X⟩) : J.yoneda.map f ≫ J.yonedaEquiv.symm x = J.yonedaEquiv.symm
      ((F.val.map f.op) x) := by
  apply J.yonedaEquiv.injective
  simp only [yonedaEquiv_comp, yonedaEquiv_symm_app_apply, Equiv.apply_symm_apply]
  rw [yonedaEquiv_yoneda_map]

lemma yonedaEquiv_symm_naturality_right (X : C) {F F' : Sheaf J (Type v)} (f : F ⟶ F')
    (x : F.val.obj ⟨X⟩) : J.yonedaEquiv.symm x ≫ f = J.yonedaEquiv.symm (f.val.app ⟨X⟩ x) := by
  apply J.yonedaEquiv.injective
  simp [yonedaEquiv_comp]

/-- See also `map_yonedaEquiv'` for a more general version. -/
lemma map_yonedaEquiv {X Y : C} {F : Sheaf J (Type v)} (f : J.yoneda.obj X ⟶ F)
    (g : Y ⟶ X) : F.val.map g.op (J.yonedaEquiv f) = f.val.app (op Y) g := by
  rw [yonedaEquiv_naturality, yonedaEquiv_comp, yonedaEquiv_yoneda_map]

/--
Variant of `map_yonedaEquiv` with general `g`. This is technically strictly more general
than `map_yonedaEquiv`, but `map_yonedaEquiv` is sometimes preferable because it
can avoid the "motive is not type correct" error.
-/
lemma map_yonedaEquiv' {X Y : Cᵒᵖ} {F : Sheaf J (Type v)} (f : J.yoneda.obj (unop X) ⟶ F)
    (g : X ⟶ Y) : F.val.map g (J.yonedaEquiv f) = f.val.app Y g.unop := by
  rw [yonedaEquiv_naturality', yonedaEquiv_comp, yonedaEquiv_yoneda_map]

lemma yonedaEquiv_symm_map {X Y : Cᵒᵖ} (f : X ⟶ Y) {F : Sheaf J (Type v)} (t : F.val.obj X) :
    J.yonedaEquiv.symm (F.val.map f t) = J.yoneda.map f.unop ≫ J.yonedaEquiv.symm t := by
  obtain ⟨u, rfl⟩ := J.yonedaEquiv.surjective t
  rw [yonedaEquiv_naturality', Equiv.symm_apply_apply, Equiv.symm_apply_apply]

/--
Two morphisms of sheaves of types `P ⟶ Q` coincide if the precompositions with morphisms
`yoneda.obj X ⟶ P` agree.
-/
lemma hom_ext_yoneda {P Q : Sheaf J (Type v)} {f g : P ⟶ Q}
    (h : ∀ (X : C) (p : J.yoneda.obj X ⟶ P), p ≫ f = p ≫ g) :
    f = g := by
  ext X x
  simpa only [yonedaEquiv_comp, Equiv.apply_symm_apply]
    using congr_arg (J.yonedaEquiv) (h _ (J.yonedaEquiv.symm x))

/-- The curried version of the Yoneda lemma for sheaves. -/
def largeCurriedYonedaLemma :
    J.yoneda.op ⋙ coyoneda ≅
      evaluation Cᵒᵖ (Type v) ⋙ (whiskeringRight _ _ _).obj uliftFunctor.{u}
      ⋙ (whiskeringLeft _ _ _).obj (sheafToPresheaf _ _) :=
  ((isoWhiskerLeft _ sheafToPresheafCompCoyonedaCompWhiskeringLeftSheafToPresheaf.symm).trans
    (isoWhiskerRight (NatIso.op J.yonedaCompSheafToPresheaf.symm)
    (_ ⋙ (whiskeringLeft _ _ _).obj _))).trans
    (isoWhiskerRight CategoryTheory.largeCurriedYonedaLemma ((whiskeringLeft _ _ _).obj _))

@[simp]
lemma largeCurriedYonedaLemma_app_app (X : C) (F : Sheaf J (Type v)) :
    (J.largeCurriedYonedaLemma.app (op X)).app F
    = (J.yonedaEquiv.trans Equiv.ulift.symm).toIso :=
  rfl

/-- A version of `yonedaEquiv` for `uliftYoneda`. -/
def uliftYonedaEquiv {X : C} {F : Sheaf J (Type (max v v'))} :
    ((uliftYoneda.{v'} J).obj X ⟶ F) ≃ F.val.obj (op X) :=
  (fullyFaithfulSheafToPresheaf _ _).homEquiv.trans CategoryTheory.uliftYonedaEquiv

@[deprecated (since := "2025-11-10")] alias yonedaULiftEquiv := uliftYonedaEquiv

theorem uliftYonedaEquiv_apply {X : C} {F : Sheaf J (Type (max v v'))}
    (f : J.uliftYoneda.obj X ⟶ F) : uliftYonedaEquiv.{v'} J f = f.val.app (op X) ⟨𝟙 X⟩ :=
  rfl

@[deprecated (since := "2025-11-10")] alias yonedaULiftEquiv_apply := uliftYonedaEquiv_apply

@[simp]
theorem uliftYonedaEquiv_symm_app_apply {X : C} {F : Sheaf J (Type (max v v'))}
    (x : F.val.obj (op X)) (Y : Cᵒᵖ) (f : Y.unop ⟶ X) :
    (J.uliftYonedaEquiv.symm x).val.app Y ⟨f⟩ = F.val.map f.op x :=
  rfl

@[deprecated (since := "2025-11-10")] alias yonedaULiftEquiv_symm_app_apply :=
  uliftYonedaEquiv_symm_app_apply

/-- See also `uliftYonedaEquiv_naturality'` for a more general version. -/
lemma uliftYonedaEquiv_naturality {X Y : C} {F : Sheaf J (Type (max v v'))}
    (f : J.uliftYoneda.obj X ⟶ F) (g : Y ⟶ X) :
      F.val.map g.op (J.uliftYonedaEquiv f) = J.uliftYonedaEquiv (J.uliftYoneda.map g ≫ f) := by
  change (f.val.app (op X) ≫ F.val.map g.op) ⟨𝟙 X⟩ = f.val.app (op Y) ⟨𝟙 Y ≫ g⟩
  rw [← f.val.naturality]
  simp [uliftYoneda]

@[deprecated (since := "2025-11-10")] alias yonedaULiftEquiv_naturality :=
  uliftYonedaEquiv_naturality

/-- Variant of `uliftYonedaEquiv_naturality` with general `g`. This is technically strictly more
general than `uliftYonedaEquiv_naturality`, but `uliftYonedaEquiv_naturality` is sometimes
preferable because it can avoid the "motive is not type correct" error. -/
lemma uliftYonedaEquiv_naturality' {X Y : Cᵒᵖ} {F : Sheaf J (Type (max v v'))}
    (f : J.uliftYoneda.obj (unop X) ⟶ F) (g : X ⟶ Y) :
    F.val.map g (J.uliftYonedaEquiv f) = J.uliftYonedaEquiv (J.uliftYoneda.map g.unop ≫ f) :=
  J.uliftYonedaEquiv_naturality _ _

@[deprecated (since := "2025-11-10")] alias yonedaULiftEquiv_naturality' :=
  uliftYonedaEquiv_naturality'

lemma uliftYonedaEquiv_comp {X : C} {F G : Sheaf J (Type (max v v'))} (α : J.uliftYoneda.obj X ⟶ F)
    (β : F ⟶ G) : J.uliftYonedaEquiv (α ≫ β) = β.val.app _ (J.uliftYonedaEquiv α) :=
  rfl

@[deprecated (since := "2025-11-10")] alias yonedaULiftEquiv_comp := uliftYonedaEquiv_comp

lemma uliftYonedaEquiv_uliftYoneda_map {X Y : C} (f : X ⟶ Y) :
    (uliftYonedaEquiv.{v'} J) (J.uliftYoneda.map f) = ⟨f⟩ := by
  rw [uliftYonedaEquiv_apply]
  simp [uliftYoneda]

@[deprecated (since := "2025-11-10")] alias yonedaULiftEquiv_yonedaULift_map :=
  uliftYonedaEquiv_uliftYoneda_map

lemma uliftYonedaEquiv_symm_naturality_left {X X' : C} (f : X' ⟶ X) (F : Sheaf J (Type (max v v')))
    (x : F.val.obj ⟨X⟩) :
    J.uliftYoneda.map f ≫ J.uliftYonedaEquiv.symm x =
      J.uliftYonedaEquiv.symm ((F.val.map f.op) x) := by
  apply J.uliftYonedaEquiv.injective
  simp only [uliftYonedaEquiv_comp, Equiv.apply_symm_apply]
  rw [uliftYonedaEquiv_uliftYoneda_map]
  rfl

@[deprecated (since := "2025-11-10")] alias yonedaULiftEquiv_symm_naturality_left :=
  uliftYonedaEquiv_symm_naturality_left

lemma uliftYonedaEquiv_symm_naturality_right (X : C) {F F' : Sheaf J (Type (max v v'))}
    (f : F ⟶ F') (x : F.val.obj ⟨X⟩) :
    J.uliftYonedaEquiv.symm x ≫ f = J.uliftYonedaEquiv.symm (f.val.app ⟨X⟩ x) := by
  apply J.uliftYonedaEquiv.injective
  simp [uliftYonedaEquiv_comp]

@[deprecated (since := "2025-11-10")] alias yonedaULiftEquiv_symm_naturality_right :=
  uliftYonedaEquiv_symm_naturality_right

/-- See also `map_yonedaEquiv'` for a more general version. -/
lemma map_uliftYonedaEquiv {X Y : C} {F : Sheaf J (Type (max v v'))}
    (f : J.uliftYoneda.obj X ⟶ F) (g : Y ⟶ X) :
    F.val.map g.op (J.uliftYonedaEquiv f) = f.val.app (op Y) ⟨g⟩ := by
  rw [uliftYonedaEquiv_naturality, uliftYonedaEquiv_comp, uliftYonedaEquiv_uliftYoneda_map]

@[deprecated (since := "2025-11-10")] alias map_yonedaULiftEquiv := map_uliftYonedaEquiv

/-- Variant of `map_uliftYonedaEquiv` with general `g`. This is technically strictly more general
than `map_uliftYonedaEquiv`, but `map_uliftYonedaEquiv` is sometimes preferable because it
can avoid the "motive is not type correct" error. -/
lemma map_uliftYonedaEquiv' {X Y : Cᵒᵖ} {F : Sheaf J (Type (max v v'))}
    (f : J.uliftYoneda.obj (unop X) ⟶ F) (g : X ⟶ Y) :
    F.val.map g (J.uliftYonedaEquiv f) = f.val.app Y ⟨g.unop⟩ := by
  rw [uliftYonedaEquiv_naturality', uliftYonedaEquiv_comp, uliftYonedaEquiv_uliftYoneda_map]

@[deprecated (since := "2025-11-10")] alias map_yonedaULiftEquiv' := map_uliftYonedaEquiv'

lemma uliftYonedaEquiv_symm_map {X Y : Cᵒᵖ} (f : X ⟶ Y) {F : Sheaf J (Type (max v v'))}
    (t : F.val.obj X) : J.uliftYonedaEquiv.symm (F.val.map f t) =
      J.uliftYoneda.map f.unop ≫ J.uliftYonedaEquiv.symm t := by
  obtain ⟨u, rfl⟩ := J.uliftYonedaEquiv.surjective t
  rw [uliftYonedaEquiv_naturality', Equiv.symm_apply_apply, Equiv.symm_apply_apply]

@[deprecated (since := "2025-11-10")] alias yonedaULiftEquiv_symm_map := uliftYonedaEquiv_symm_map

/-- Two morphisms of sheaves of types `P ⟶ Q` coincide if the precompositions
with morphisms `uliftYoneda.obj X ⟶ P` agree. -/
lemma hom_ext_uliftYoneda {P Q : Sheaf J (Type (max v v'))} {f g : P ⟶ Q}
    (h : ∀ (X : C) (p : J.uliftYoneda.obj X ⟶ P), p ≫ f = p ≫ g) :
    f = g := by
  ext X x
  simpa only [uliftYonedaEquiv_comp, Equiv.apply_symm_apply]
    using congr_arg (J.uliftYonedaEquiv) (h _ (J.uliftYonedaEquiv.symm x))

@[deprecated (since := "2025-11-10")] alias hom_ext_yonedaULift := hom_ext_uliftYoneda

/-- A variant of the curried version of the Yoneda lemma with a raise in the universe level. -/
def largeCurriedUliftYonedaLemma :
    J.uliftYoneda.op ⋙ coyoneda ≅
      evaluation Cᵒᵖ (Type max v v') ⋙ (whiskeringRight _ _ _).obj uliftFunctor.{u}
      ⋙ (whiskeringLeft _ _ _).obj (sheafToPresheaf _ _) :=
  ((isoWhiskerLeft (J.yoneda.op ⋙ (sheafCompose J _).op)
    sheafToPresheafCompCoyonedaCompWhiskeringLeftSheafToPresheaf.symm).trans
    (isoWhiskerRight (NatIso.op (J.uliftYonedaCompSheafToPresheaf.symm))
    (_ ⋙ (whiskeringLeft _ _ _).obj _))).trans
    (isoWhiskerRight CategoryTheory.uliftYonedaOpCompCoyoneda
    ((whiskeringLeft _ _ _).obj _))

@[simp]
lemma largeCurriedUliftYonedaLemma_app_app (X : C) (F : Sheaf J (Type (max v v'))) :
    (J.largeCurriedUliftYonedaLemma.app (op X)).app F
    = (J.uliftYonedaEquiv.trans Equiv.ulift.symm).toIso :=
  rfl

abbrev familyOfElementsPtVal {X : C} {S : Sieve X}
    (s : Limits.Cocone (S.arrows.diagram ⋙ J.yoneda)) :
    S.arrows.FamilyOfElements s.pt.val :=
  (fun _ f hf => J.yonedaEquiv (s.ι.app ⟨Over.mk f, hf⟩))

abbrev familyOfElementsPtVal' {X : C} {S : Sieve X}
    (s : Limits.Cocone (S.arrows.diagram ⋙ GrothendieckTopology.uliftYoneda.{u} J)) :
    S.arrows.FamilyOfElements s.pt.val :=
  (fun _ f hf => J.uliftYonedaEquiv (s.ι.app ⟨Over.mk f, hf⟩))

theorem familyOfElementsPtVal_compatible {X : C} {S : Sieve X}
    (s : Limits.Cocone (S.arrows.diagram ⋙ J.yoneda)) :
    (J.familyOfElementsPtVal s).Compatible := by
  refine (Presieve.compatible_iff_sieveCompatible _).2 (fun Y Z f g hf => ?_)
  rw [yonedaEquiv_naturality]
  let : ({ obj := Over.mk (g ≫ f), property := S.downward_closed hf g } : S.arrows.category)
      ⟶ { obj := Over.mk f, property := hf} :=
    Over.homMk g
  simp only [id_obj, ← s.w this, comp_obj, ObjectProperty.ι_obj, Over.forget_obj,
    Over.mk_left, const_obj_obj, Functor.comp_map, ObjectProperty.ι_map, Over.forget_map,
    EmbeddingLike.apply_eq_iff_eq]
  rfl

theorem familyOfElementsPtVal_compatible' {X : C} {S : Sieve X}
    (s : Limits.Cocone (S.arrows.diagram ⋙ GrothendieckTopology.uliftYoneda.{u} J)) :
    (J.familyOfElementsPtVal' s).Compatible := by
  refine (Presieve.compatible_iff_sieveCompatible _).2 (fun Y Z f g hf => ?_)
  rw [uliftYonedaEquiv_naturality]
  let : ({ obj := Over.mk (g ≫ f), property := S.downward_closed hf g } : S.arrows.category)
      ⟶ { obj := Over.mk f, property := hf} :=
    Over.homMk g
  simp only [id_obj, ← s.w this, comp_obj, ObjectProperty.ι_obj, Over.forget_obj,
    Over.mk_left, const_obj_obj, Functor.comp_map, ObjectProperty.ι_map, Over.forget_map,
    EmbeddingLike.apply_eq_iff_eq]
  rfl

@[simps]
def compatibleYonedaFamily_toCocone (F : Sheaf J (Type v)) {X : C} (R : Presieve X)
    (x : Presieve.FamilyOfElements F.val R) (hx : x.Compatible) :
    Limits.Cocone (R.diagram ⋙ J.yoneda) where
  pt := F
  ι := {
    app := fun ⟨f, hf⟩ => J.yonedaEquiv.invFun (x f.hom hf)
    naturality := fun ⟨f, hf⟩ ⟨g, hg⟩ φ => by
      simp [J.yonedaEquiv_symm_naturality_left, hx φ.left (𝟙 _) hg hf]
    }

@[simps]
def compatibleUliftYonedaFamily_toCocone (F : Sheaf J (Type max u v)) {X : C} (R : Presieve X)
    (x : Presieve.FamilyOfElements F.val R) (hx : x.Compatible) :
    Limits.Cocone (R.diagram ⋙ J.uliftYoneda) where
  pt := F
  ι := {
    app := fun ⟨f, hf⟩ => J.uliftYonedaEquiv.invFun (x f.hom hf)
    naturality := fun ⟨f, hf⟩ ⟨g, hg⟩ φ => by
      simp [J.uliftYonedaEquiv_symm_naturality_left, hx φ.left (𝟙 _) hg hf]
    }

theorem isSheaf_sup (K L : GrothendieckTopology C) (P : Cᵒᵖ ⥤ Type max u v) :
    Presieve.IsSheaf (K ⊔ L) P ↔ Presieve.IsSheaf K P ∧ Presieve.IsSheaf L P := by
  rw [← (Coverage.gi C).l_u_eq K, ← (Coverage.gi C).l_u_eq L, ← (Coverage.gi C).gc.l_sup,
    Presieve.isSheaf_sup, (Coverage.gi C).l_u_eq K, (Coverage.gi C).l_u_eq L]

omit [J.Subcanonical] in
theorem mem_of_isSheafFor_pullback (X : C) (S : Sieve X)
    (hS : ∀ (F : Sheaf J (Type max u v)) {Y : C} {f : Y ⟶ X},
      Presieve.IsSheafFor F.val (S.pullback f).arrows) :
    S ∈ J X := by
  let J₂ := J ⊔ (S.arrows.skyscraperPrecoverage.toGrothendieck')
  have : J = J₂ := by
    refine topology_eq_iff_same_sheaves.2 (fun P => ?_)
    constructor <;> intro hP
    · unfold J₂
      refine (isSheaf_sup _ _ _).2 ⟨hP, ?_⟩
      rw [S.arrows.skyscraperPrecoverage.isSheaf_toGrothendieck'_iff]
      intro Y Z f R hR
      cases hR
      rw [Sieve.generate_sieve]
      exact hS ⟨P, (isSheaf_iff_isSheaf_of_type J P).2 hP⟩
    · exact Presieve.isSheaf_of_le P le_sup_left hP
  rw [this]
  apply le_sup_right (a := J)
  rw [← S.generate_sieve]
  apply Precoverage.generate_mem_toGrothendieck'
  simp

@[simps!]
def _root_.CategoryTheory.Sieve.pullbackFunctorNatTrans {X Y : C} (S : Sieve X) (f : Y ⟶ X) :
    (S.pullback f).functor ⟶ S.functor where
  app Z := fun ⟨g, hg⟩ => ⟨g ≫ f, hg⟩

theorem _root_.CategoryTheory.Sieve.isPullback_functorInclusion_pullback {X Y : C} (S : Sieve X)
    (f : Y ⟶ X) :
    IsPullback (S.pullback f).functorInclusion (S.pullbackFunctorNatTrans f)
      (CategoryTheory.yoneda.map f) S.functorInclusion := by
  have (t : Limits.PullbackCone (CategoryTheory.yoneda.map f) S.functorInclusion) (Z : Cᵒᵖ)
      (s : t.pt.obj Z) : t.fst.app Z s ≫ f = (t.snd.app Z s).1 := by
    change (t.fst ≫ CategoryTheory.yoneda.map f).app Z s = (t.snd ≫ S.functorInclusion).app Z s
    rw [t.condition]
  refine IsPullback.mk { w := rfl } ⟨Limits.PullbackCone.IsLimit.mk _ ?_ ?_ ?_ ?_⟩ <;> intro t
  · refine NatTrans.mk (fun Z => ?_) (fun Z Z' g => ?_)
    · refine fun s => ⟨t.fst.app Z s, ?_⟩
      rw [Sieve.pullback_apply, this]
      exact (t.snd.app Z s).2
    · ext s
      apply Subtype.ext
      change (t.pt.map g ≫ t.fst.app Z') s = _
      rw [t.fst.naturality]
      rfl
  · ext Z s
    rfl
  · ext Z s
    apply Subtype.ext
    simp [this]
  · intro m hm _
    ext Z s
    apply Subtype.ext
    change (m ≫ (Sieve.pullback f S).functorInclusion).app Z s = t.fst.app Z s
    rw [hm]

noncomputable def _root_.CategoryTheory.Sieve.pullbackFunctorIsoPullback {X Y : C} (S : Sieve X)
    (f : Y ⟶ X) :
    (Sieve.pullback f S).functor ≅
      Limits.pullback (CategoryTheory.yoneda.map f) S.functorInclusion :=
  (S.isPullback f).isoPullback

abbrev _root_.CategoryTheory.Sieve.functorDiagram {X : C} (S : Sieve X) :
    S.arrows.category ⥤ Cᵒᵖ ⥤ Type max u v :=
  S.arrows.diagram ⋙ CategoryTheory.uliftYoneda

@[simps!]
def _root_.CategoryTheory.Sieve.functorCocone {X : C} (S : Sieve X) :
    Limits.Cocone S.functorDiagram where
  pt := S.functor ⋙ uliftFunctor
  ι := {
      app := fun ⟨⟨Y, _, f⟩, hY⟩ =>
        NatTrans.mk (fun Z ⟨g⟩ => { down := ⟨g ≫ f, S.downward_closed hY g⟩ })
      naturality := by
        intro ⟨⟨Y, _, g⟩, hY⟩ ⟨⟨Z, _, h⟩, hY⟩ ⟨f, _, hf⟩
        simp only [id_obj, const_obj_obj, Functor.id_map, const_obj_map, Category.comp_id] at hf
        ext W ⟨i⟩
        simp [hf]
    }

theorem isRepresentable_of_natIso' (F : Cᵒᵖ ⥤ Type*) {G} (i : F ≅ G) [F.IsRepresentable] :
    G.IsRepresentable :=
  (F.representableBy.ofIso i).isRepresentable

variable [HasWeakSheafify (Sheaf.canonicalTopology C) (Type max u v)] (F : Cᵒᵖ ⥤ Type max u v)

@[simp]
def _root_.CategoryTheory.sectionProperty : ObjectProperty (Over F) :=
  fun G => IsRepresentable G.1

abbrev _root_.CategoryTheory.sectionCategory := (sectionProperty F).FullSubcategory

instance : Category (sectionCategory F) := ObjectProperty.FullSubcategory.category _

instance (G : sectionCategory F) : IsRepresentable G.1.1 := G.2

-- TODO : comprendre pourquoi ces simp lemmas n'existent pas déjà

omit [J.Subcanonical] [HasWeakSheafify (Sheaf.canonicalTopology C) (Type max u v)] in
@[simp]
lemma _root_.CategoryTheory.section_left_id (G : sectionCategory F) :
    CommaMorphism.left (𝟙 G) = 𝟙 G.obj.left :=
  rfl -- Comma.id_left ?

omit [J.Subcanonical] [HasWeakSheafify (Sheaf.canonicalTopology C) (Type max u v)] in
@[simp]
lemma _root_.CategoryTheory.section_left_comp {G₁ G₂ G₃ : sectionCategory F} (f : G₁ ⟶ G₂)
    (g : G₂ ⟶ G₃) : CommaMorphism.left (f ≫ g) = f.left ≫ g.left :=
  rfl

@[simps! obj_left obj_hom]
def _root_.CategoryTheory.sectionMk {X : C} (s : F.obj (Opposite.op X)) : sectionCategory F where
  obj := Over.mk (CategoryTheory.uliftYonedaEquiv.symm s)
  property := by
    unfold sectionProperty
    rw [Over.mk_left]
    infer_instance

@[simps!]
def _root_.CategoryTheory.sectionMkHom (G : sectionCategory F) {X : Cᵒᵖ} (s : G.obj.left.obj X) :
    sectionMk F (G.obj.hom.app X s) ⟶ G := by
  refine Over.homMk (CategoryTheory.uliftYonedaEquiv.symm s) ?_
  simp only [id_obj, const_obj_obj, sectionMk_obj_left, op_unop, sectionMk_obj_hom]
  rw [Equiv.eq_symm_apply, CategoryTheory.uliftYonedaEquiv_comp, Equiv.apply_symm_apply]

@[simps! left_app]
def _root_.CategoryTheory.sectionHomMk {X Y : C} (s : F.obj (Opposite.op X)) (f : Y ⟶ X) :
    sectionMk F (F.map f.op s) ⟶ sectionMk F s :=
  Over.homMk (CategoryTheory.uliftYoneda.map f)

open Limits in
@[simps!]
def _root_.CategoryTheory.sectionCocone : Cocone ((sectionProperty F).ι ⋙ Over.forget _) where
  pt := F
  ι := NatTrans.mk (fun ⟨X, _⟩ => X.hom)

def _root_.CategoryTheory.isColimitSectionCocone : Limits.IsColimit (sectionCocone F) where
  desc c := by
    refine NatTrans.mk (fun X s => (c.ι.app (sectionMk F s)).app X { down := 𝟙 _ }) ?_
    intro X Y f
    ext s
    let ι_app : _ ⟶ c.pt := c.ι.app (sectionMk F s)
    change (c.ι.app (sectionMk F (F.map f.unop.op s))).app Y _ = (ι_app.app X ≫ c.pt.map f) _
    rw [← ι_app.naturality, ← c.w (sectionHomMk F s f.unop)]
    simp [ι_app]
  fac c := by
    intro G
    ext Y s
    simp [← c.w (sectionMkHom F G s)]
  uniq c m h := by
    ext X s
    simp only [← h, sectionCocone_ι_app, FunctorToTypes.comp, sectionMk_obj_hom,
      uliftYonedaEquiv_symm_apply_app, op_id, FunctorToTypes.map_id_apply]

instance : Limits.HasColimit ((sectionProperty F).ι ⋙ Over.forget _) where
  exists_colimit := ⟨⟨_, isColimitSectionCocone F⟩⟩

omit [J.Subcanonical] [HasWeakSheafify (Sheaf.canonicalTopology C) (Type max u v)] in
variable [HasWeakSheafify J (Type max u v)] in
theorem isColimitPresheafToSheafMapCoconeSectionCocone :
    Nonempty (Limits.IsColimit
      ((presheafToSheaf J (Type max u v)).mapCocone (sectionCocone F))) :=
  (Adjunction.leftAdjoint_preservesColimits
    (sheafificationAdjunction J (Type max u v))).preservesColimitsOfShape.preservesColimit.preserves
    (isColimitSectionCocone F)

abbrev _root_.CategoryTheory.Sieve.uliftFunctor {X : C} (S : Sieve X) : Cᵒᵖ ⥤ Type max u v :=
  S.functor ⋙ CategoryTheory.uliftFunctor.{u}

@[simps! app]
def _root_.CategoryTheory.Sieve.uliftFunctorInclusion {X : C} (S : Sieve X) :
    S.uliftFunctor ⟶ CategoryTheory.uliftYoneda.obj.{u} X :=
  ((whiskeringRight _ _ _).obj uliftFunctor.{u}).map S.functorInclusion

omit [HasWeakSheafify (Sheaf.canonicalTopology C) (Type max u v)] in
/-- The presheaf induced by a sieve is a subobject of the yoneda embedding. -/
instance _root_.CategoryTheory.Sieve.uliftFunctorInclusion_is_mono {X : C} (S : Sieve X) :
    Mono S.uliftFunctorInclusion :=
  ⟨fun f g h => by
    ext Y y
    refine ULift.ext _ _ (Subtype.ext_iff.2 ?_)
    simpa using congr_fun (NatTrans.congr_app h Y) y⟩

omit [HasWeakSheafify (Sheaf.canonicalTopology C) (Type max u v)] in
theorem _root_.CategoryTheory.Sieve.uliftYonedaEquiv_comp_uliftFunctorInclusion {X : C}
    (S : Sieve X) {Y : C} (g : S.uliftFunctor.obj (Opposite.op Y)) :
    CategoryTheory.uliftYonedaEquiv.symm g ≫ S.uliftFunctorInclusion =
      CategoryTheory.uliftYoneda.map g.down.1 :=
  rfl

@[simps]
def _root_.CategoryTheory.Sieve.sieveOfUliftSubfunctor {X : C} {R : Cᵒᵖ ⥤ Type max u v}
    (f : R ⟶ CategoryTheory.uliftYoneda.obj X) : Sieve X where
  arrows Y g := ∃ t, f.app (op Y) t = { down := g }
  downward_closed := by
    rintro Y Z _ ⟨t, ht⟩ g
    refine ⟨R.map g.op t, ?_⟩
    rw [FunctorToTypes.naturality _ _ f, ht]
    simp

omit [HasWeakSheafify (Sheaf.canonicalTopology C) (Type max u v)] in
theorem _root_.CategoryTheory.Sieve.sieveOfUliftSubfunctor_uliftFunctorInclusion {X : C}
    {S : Sieve X} : Sieve.sieveOfUliftSubfunctor (S.uliftFunctorInclusion) = S := by
  ext
  simp only [Sieve.uliftFunctorInclusion_app, Sieve.sieveOfUliftSubfunctor_apply]
  constructor
  · rintro ⟨⟨f, hf⟩, h⟩
    simp only [uliftYoneda_obj_obj, yoneda_obj_obj, ULift.up.injEq] at h
    simpa [← h]
  · intro hf
    exact ⟨⟨_, hf⟩, rfl⟩

@[simps!]
def _root_.CategoryTheory.Sieve.pullbackUliftFunctorNatTrans {X Y : C} (S : Sieve X) (f : Y ⟶ X) :
    (S.pullback f).uliftFunctor ⟶ S.uliftFunctor where
  app Z := fun ⟨g, hg⟩ => ⟨g ≫ f, hg⟩

omit [HasWeakSheafify (Sheaf.canonicalTopology C) (Type (max u v))] in
theorem _root_.CategoryTheory.Sieve.isPullback_uliftFunctorInclusion_pullback {X Y : C}
    (S : Sieve X) (f : Y ⟶ X) :
    IsPullback (S.pullback f).uliftFunctorInclusion (S.pullbackUliftFunctorNatTrans f)
      (CategoryTheory.uliftYoneda.map f) S.uliftFunctorInclusion := by
  have (t : Limits.PullbackCone (CategoryTheory.uliftYoneda.map f) S.uliftFunctorInclusion)
      (Z : Cᵒᵖ) (s : t.pt.obj Z) : (t.fst.app Z s).down ≫ f = (t.snd.app Z s).down.val := by
    change ((t.fst ≫ CategoryTheory.uliftYoneda.map f).app Z s).down =
      ((t.snd ≫ S.uliftFunctorInclusion).app Z s).down
    rw [t.condition]
  refine IsPullback.mk { w := rfl } ⟨Limits.PullbackCone.IsLimit.mk _ ?_ ?_ ?_ ?_⟩ <;> intro t
  · refine NatTrans.mk (fun Z => ?_) (fun Z Z' g => ?_)
    · refine fun s => ⟨(t.fst.app Z s).down, ?_⟩
      rw [Sieve.pullback_apply, this]
      exact (t.snd.app Z s).down.2
    · ext s
      refine ULift.ext _ _ (Subtype.ext ?_)
      change ((t.pt.map g ≫ t.fst.app Z') s).down = _
      rw [t.fst.naturality]
      rfl
  · ext Z s
    rfl
  · ext Z s
    refine ULift.ext _ _ (Subtype.ext ?_)
    simp [this]
  · intro m hm _
    ext Z s
    refine ULift.ext _ _ (Subtype.ext ?_)
    change ((m ≫ (Sieve.pullback f S).uliftFunctorInclusion).app Z s).down = (t.fst.app Z s).down
    rw [hm]

omit [HasWeakSheafify (Sheaf.canonicalTopology C) (Type max u v)] in
theorem _root_.CategoryTheory.Sieve.arrows_iff_exists_map_functor {X : C} (S : Sieve X) {Y : C}
    (f : Y ⟶ X) :
    S.arrows f ↔
      ∃ t : CategoryTheory.uliftYoneda.obj Y ⟶ S.uliftFunctor, t ≫ S.uliftFunctorInclusion =
        CategoryTheory.uliftYoneda.map f := by
  nth_rw 1 [← S.sieveOfUliftSubfunctor_uliftFunctorInclusion]
  constructor
  · refine fun ⟨t, ht⟩ => ⟨CategoryTheory.uliftYonedaEquiv.symm t, ?_⟩
    ext Z g
    simp only [uliftYoneda_obj_obj, Sieve.uliftFunctorInclusion_app, yoneda_obj_obj,
      ULift.up.injEq] at ht
    simp only [uliftYoneda_obj_obj, comp_obj, Sieve.functor_obj, uliftFunctor_obj,
      FunctorToTypes.comp, Sieve.uliftFunctorInclusion_app, ← ht, uliftYoneda_map_app,
      ULift.up.injEq]
    rfl
  · refine fun ⟨t, ht⟩ => ⟨CategoryTheory.uliftYonedaEquiv t, ?_⟩
    have : (t ≫ S.uliftFunctorInclusion).app (op Y) { down := 𝟙 Y} =
        (CategoryTheory.uliftYoneda.map f).app (op Y) { down := 𝟙 Y} := by
      rw [ht]
    simp only [uliftYoneda_obj_obj, yoneda_obj_obj, FunctorToTypes.comp,
      Sieve.uliftFunctorInclusion_app, uliftYoneda_map_app, Category.id_comp,
      ULift.up.injEq] at this
    rw [← this]
    rfl

@[simps! app]
def _root_.CategoryTheory.Sieve.homFunctor {X Y : C} {S : Sieve X} {f : Y ⟶ X} (hf : S f) :
    CategoryTheory.uliftYoneda.obj Y ⟶ S.uliftFunctor :=
  NatTrans.mk (fun _ g => { down := ⟨g.down ≫ f, S.downward_closed hf g.down⟩ })

def _root_.CategoryTheory.Sieve.functorSectionPropertyFullSubcategory {X : C} (S : Sieve X) :
    S.arrows.category ⥤ (sectionProperty S.uliftFunctor).FullSubcategory where
  obj f := by
    refine { obj := Over.mk (S.homFunctor f.property), property := ?_ }
    simp only [sectionProperty, Over.mk_left]
    infer_instance
  map φ := Over.homMk (CategoryTheory.uliftYoneda.map φ.left)
  map_id _ := Over.OverMorphism.ext (by simp [ObjectProperty.FullSubcategory.id_def])
  map_comp _ _ := Over.OverMorphism.ext (by simp [ObjectProperty.FullSubcategory.comp_def])

omit [HasWeakSheafify (Sheaf.canonicalTopology C) (Type max u v)] in
@[simp]
theorem _root_.CategoryTheory.Sieve.app_comp_down_val {X : C} (S : Sieve X) {Y : C}
    (F : CategoryTheory.uliftYoneda.{u}.obj Y ⟶ S.uliftFunctor) {Z : Cᵒᵖ} (f : Z.unop ⟶ Y)
    {Z' : Cᵒᵖ} (g : Z'.unop ⟶ Z.unop) :
    (F.app Z' { down := g ≫ f }).down.val = g ≫ (F.app Z { down := f }).down.val :=
  congr(($(F.naturality g.op) { down := f }).down.val)

omit [HasWeakSheafify (Sheaf.canonicalTopology C) (Type max u v)] in
theorem _root_.CategoryTheory.Sieve.app_down_val {X : C} (S : Sieve X) {Y : C}
    (F : CategoryTheory.uliftYoneda.{u}.obj Y ⟶ S.uliftFunctor) {Z : Cᵒᵖ} (f : Z.unop ⟶ Y) :
    (F.app Z { down := f }).down.val =
      f ≫ (ULiftYoneda.fullyFaithful C).preimage (F ≫ S.uliftFunctorInclusion) := by
  apply (ULiftYoneda.fullyFaithful.{u} _).map_injective
  ext Z' t
  simp [S.app_comp_down_val]

omit [HasWeakSheafify (Sheaf.canonicalTopology C) (Type max u v)] in
theorem _root_.CategoryTheory.Sieve.app_down_val' {X : C} (S : Sieve X) {Y : C}
    (F : CategoryTheory.uliftYoneda.{u}.obj Y ⟶ S.uliftFunctor) {Z : Cᵒᵖ}
    (f : ULift.{u} (Z.unop ⟶ Y)) :
    (F.app Z f).down.val =
      f.down ≫ (ULiftYoneda.fullyFaithful C).preimage (F ≫ S.uliftFunctorInclusion) :=
  S.app_down_val F f.down

-- useless
@[simps!]
noncomputable def _root_.CategoryTheory.Sieve.sectionCategoryUliftFunctor {X : C} (S : Sieve X) :
    sectionCategory S.uliftFunctor ≌ S.arrows.category := by
  unfold Presieve.category
  fapply Equivalence.mk
  · refine ObjectProperty.lift _ ?_ ?_
    · refine Functor.mk ?_ ?_ ?_ ?_
      · intro ⟨F, (_ : F.left.IsRepresentable)⟩
        exact Over.mk ((CategoryTheory.ULiftYoneda.fullyFaithful _).preimage
          (F.left.uliftReprW.hom ≫ F.hom ≫ S.uliftFunctorInclusion))
      · intro ⟨F, (_ : F.left.IsRepresentable)⟩ ⟨G, (_ : G.left.IsRepresentable)⟩ f
        refine Over.homMk ((CategoryTheory.ULiftYoneda.fullyFaithful _).preimage
          (F.left.uliftReprW.hom ≫ f.left ≫ G.left.uliftReprW.inv)) ?_
        simp only [Over.mk_left, const_obj_obj, Over.mk_hom]
        apply (ULiftYoneda.fullyFaithful C).map_injective
        rw [map_comp, (ULiftYoneda.fullyFaithful C).map_preimage,
          (ULiftYoneda.fullyFaithful C).map_preimage, (ULiftYoneda.fullyFaithful C).map_preimage]
        simp
      · intro F
        have : CommaMorphism.left (𝟙 F) = 𝟙 F.obj.left := rfl
        exact Over.OverMorphism.ext (by simp [this])
      · intro _ _ _ f g
        have : (f ≫ g).left = f.left ≫ g.left := rfl
        exact Over.OverMorphism.ext (by simp [this, ← FullyFaithful.preimage_comp])
    · exact fun F => (S.arrows_iff_exists_map_functor _).2
        ⟨F.obj.left.uliftReprW.hom ≫ F.obj.hom, by simp⟩
  · refine ObjectProperty.lift _ ?_ ?_
    · refine Functor.mk ?_ ?_ ?_ ?_
      · exact fun ⟨f, hf⟩ => Over.mk (CategoryTheory.uliftYonedaEquiv.symm { down := ⟨f.hom, hf⟩ })
      · intro ⟨f, hf⟩ ⟨g, hg⟩ φ
        refine Over.homMk (CategoryTheory.uliftYoneda.map φ.left) ?_
        have : { down := ⟨f.hom, hf⟩ } = S.uliftFunctor.map φ.left.op { down := ⟨g.hom, hg⟩ } := by
          apply ULift.ext
          simp [Sieve.functor]
        simp only [id_obj, comp_obj, Sieve.functor_obj, uliftFunctor_obj, Over.mk_left,
          const_obj_obj, Over.mk_hom, this]
        let t : S.uliftFunctor.obj (op g.left) := { down := ⟨g.hom, hg⟩ }
        exact (CategoryTheory.uliftYonedaEquiv_symm_map φ.left.op t).symm
      · intro f
        have : CommaMorphism.left (𝟙 f) = 𝟙 f.obj.left := rfl
        exact Over.OverMorphism.ext (by simp [this])
      · intro _ _ _ φ ψ
        have : (φ ≫ ψ).left = φ.left ≫ ψ.left := rfl
        exact Over.OverMorphism.ext (by simp [this])
    · intro ⟨f, hf⟩
      simp only [sectionProperty, Over.mk_left]
      infer_instance
  · refine NatIso.ofComponents ?_ ?_
    · intro ⟨F, (_ : F.left.IsRepresentable)⟩
      refine ObjectProperty.isoMk _ (Over.isoMk F.left.uliftReprW.symm ?_)
      apply (cancel_mono S.uliftFunctorInclusion).1
      simp only [id_obj, ObjectProperty.ι_obj, const_obj_obj, Over.mk_left, comp_obj,
        Sieve.functor_obj, uliftFunctor_obj, ObjectProperty.lift_obj_obj, Over.mk_hom, Iso.symm_hom,
        Category.assoc]
      change _ ≫ CategoryTheory.uliftYonedaEquiv.symm (_ : S.uliftFunctor.obj _) ≫ _ = _
      rw [S.uliftYonedaEquiv_comp_uliftFunctorInclusion]
      simp
    · refine fun _ => Over.OverMorphism.ext ?_
      change _ ≫ _ = _ ≫ _
      simp
  · refine NatIso.ofComponents ?_ ?_
    · intro ⟨f, hf⟩
      refine ObjectProperty.isoMk _ (Over.isoMk reprXUliftYoneda ?_)
      apply (ULiftYoneda.fullyFaithful.{u} _).map_injective
      simp only [comp_obj, Over.mk_left, ObjectProperty.ι_obj, ObjectProperty.lift_obj_obj,
        Over.mk_hom, map_comp, uliftReprWYoneda, FullyFaithful.map_preimage]
      rfl
    · refine fun _ => Over.OverMorphism.ext ?_
      change _ ≫ _ = _ ≫ _
      simp [uliftReprWYoneda]

@[simps]
def _root_.CategoryTheory.Sieve.uliftFunctorMk {X : C} (S : Sieve X) (f : S.arrows.category) :
    S.uliftFunctor.obj (Opposite.op f.obj.left) :=
  { down := ⟨f.obj.hom, f.property⟩ }

@[simps!]
noncomputable def _root_.CategoryTheory.Sieve.costructuredArrowUliftYoneda {X : C} (S : Sieve X) :
    CostructuredArrow CategoryTheory.uliftYoneda.{u} S.uliftFunctor ≌ S.arrows.category where
  functor := by
    refine ObjectProperty.lift _ ?_ ?_
    · exact CostructuredArrow.map S.uliftFunctorInclusion ⋙
        (CostructuredArrow.equivOver _ _ (ULiftYoneda.fullyFaithful _)).functor
    · exact fun _ => (S.arrows_iff_exists_map_functor _).2 (by simp)
  inverse := by
    refine toCostructuredArrow S.arrows.diagram _ _ ?_ ?_
    · exact fun f => CategoryTheory.uliftYonedaEquiv.symm (S.uliftFunctorMk f)
    · intro f g φ
      simpa [Sieve.functor] using
        (CategoryTheory.uliftYonedaEquiv_symm_map.{u} φ.left.op (S.uliftFunctorMk g)).symm
  unitIso := NatIso.ofComponents (fun _ => by
    refine CostructuredArrow.isoMk (Iso.refl _) ?_
    ext Y g
    simpa using (uliftYonedaEquiv_symm_apply_app _ _ _).trans
        (ULift.ext _ _ (Subtype.ext (by simp [Sieve.app_down_val']))))
  counitIso := NatIso.ofComponents (fun _ => ObjectProperty.isoMk _ (Over.isoMk (Iso.refl _))) (by
    refine fun _ => Over.OverMorphism.ext ?_
    simp
    change _ ≫ _ = _ ≫ _
    simp)
  functor_unitIso_comp := by
    refine fun _ => Over.OverMorphism.ext ?_
    change _ ≫ _ = 𝟙 _
    simp

noncomputable def _root_.CategoryTheory.Sieve.uliftFunctorElements {X : C} (S : Sieve X) :
    S.uliftFunctor.Elementsᵒᵖ ≌ S.arrows.category :=
  (CategoryOfElements.costructuredArrowULiftYonedaEquivalence _).trans
    S.costructuredArrowUliftYoneda

-- useless
@[simps!]
noncomputable def _root_.CategoryTheory.Sieve.sectionCategoryUliftFunctorCompFunctorDiagram {X : C}
    (S : Sieve X) : S.sectionCategoryUliftFunctor.functor ⋙ S.functorDiagram ≅
      (sectionProperty S.uliftFunctor).ι ⋙ Over.forget _ :=
  NatIso.ofComponents (fun ⟨F, (_ : F.left.IsRepresentable)⟩ => F.left.uliftReprW)

@[simps!]
noncomputable def _root_.CategoryTheory.Sieve.uliftFunctorElementsCompFunctorDiagram {X : C}
    (S : Sieve X) : S.uliftFunctorElements.functor ⋙ S.functorDiagram ≅
      Presheaf.functorToRepresentables S.uliftFunctor :=
  NatIso.ofComponents fun _ => Iso.refl _

-- useless
noncomputable def _root_.CategoryTheory.Sieve.functorCoconeWhiskerSectionCategoryUliftFunctor
    {X : C} (S : Sieve X) :
    S.functorCocone.whisker S.sectionCategoryUliftFunctor.functor ≅
      (Limits.Cocones.precompose S.sectionCategoryUliftFunctorCompFunctorDiagram.hom).obj
      (sectionCocone S.uliftFunctor) := by
  refine Limits.Cocones.ext (Iso.refl _) ?_
  intro F
  ext Y f
  refine ULift.ext _ _ (Subtype.ext ?_)
  change _ ≫ _ = ((F.obj.left.uliftReprW.hom ≫ F.obj.hom).app Y _).down.val
  rw [← ULift.up_down f, S.app_down_val]
  rfl

@[simps!]
noncomputable def _root_.CategoryTheory.Sieve.functorCoconeWhiskerUliftFunctorElements {X : C}
    (S : Sieve X) :
    S.functorCocone.whisker S.uliftFunctorElements.functor ≅
      (Limits.Cocones.precompose S.uliftFunctorElementsCompFunctorDiagram.hom).obj
      (Presheaf.coconeOfRepresentable S.uliftFunctor) := by
  refine Limits.Cocones.ext (Iso.refl _) ?_
  intro x
  ext Y f
  refine ULift.ext _ _ (Subtype.ext ?_)
  simp [Sieve.uliftFunctorElements, ← S.app_down_val]
  rfl

@[simps!]
noncomputable def _root_.CategoryTheory.Sieve.isColimitFunctorCocone {X : C} (S : Sieve X) :
    Limits.IsColimit S.functorCocone :=
  Limits.IsColimit.ofWhiskerEquivalence _
    (Limits.IsColimit.ofIsoColimit ((Limits.IsColimit.precomposeHomEquiv _ _).2
      (Presheaf.colimitOfRepresentable _)) S.functorCoconeWhiskerUliftFunctorElements.symm)

lemma _root_.CategoryTheory.Sieve.isColimitFunctorCocone_desc_uliftYoneda {X : C} (S : Sieve X) :
    S.isColimitFunctorCocone.desc (CategoryTheory.uliftYoneda.{u}.mapCocone S.arrows.cocone) =
      S.uliftFunctorInclusion := by
  simp [Sieve.isColimitFunctorCocone, Limits.IsColimit.ofWhiskerEquivalence,
    Limits.IsColimit.ofLeftAdjoint]

variable [HasWeakSheafify J (Type max u v)] in
theorem fkemzjf {X : C} (S : Sieve X) :
    Nonempty (Limits.IsColimit ((presheafToSheaf J (Type max u v)).mapCocone S.functorCocone)) :=
  sorry

variable [HasSheafify J (Type max u v)]

open Limits

lemma _root_.CategoryTheory.Limits.IsColimit.nonempty_isColimit_iff_isIso_desc {J : Type*}
    [Category J] {C : Type*} [Category C] {F : J ⥤ C} {s t : Cocone F} (hs : IsColimit s) :
    Nonempty (IsColimit t) ↔ IsIso (hs.desc t) :=
  ⟨fun ⟨ht⟩ ↦ ⟨ht.desc s, hs.hom_ext (by simp), ht.hom_ext (by simp)⟩,
    fun h ↦ ⟨hs.ofPointIso⟩⟩

omit [J.Subcanonical] [HasWeakSheafify (Sheaf.canonicalTopology C) (Type (max u v))] in
theorem isIso_presheafToSheaf_uliftFunctorInclusion_iff {X : C} (S : Sieve X) :
    IsIso ((presheafToSheaf J (Type max u v)).map S.uliftFunctorInclusion) ↔
    Nonempty (IsColimit
      ((CategoryTheory.uliftYoneda.{u} ⋙ presheafToSheaf J _).mapCocone S.arrows.cocone)) := by
  have h := isColimitOfPreserves (presheafToSheaf J _) S.isColimitFunctorCocone
  rw [h.nonempty_isColimit_iff_isIso_desc]
  congr!
  refine h.hom_ext (fun f => ?_)
  rw [h.fac]
  simp [← Functor.map_comp]
  rfl

omit [HasWeakSheafify (Sheaf.canonicalTopology C) (Type (max u v))] in
theorem isIso_presheafToSheaf_uliftFunctorInclusion_iff' {X : C} (S : Sieve X) :
    IsIso ((presheafToSheaf J (Type max u v)).map S.uliftFunctorInclusion) ↔
    Nonempty (IsColimit ((GrothendieckTopology.uliftYoneda.{u} J).mapCocone S.arrows.cocone)) := by
  rw [isIso_presheafToSheaf_uliftFunctorInclusion_iff]
  refine Equiv.nonempty_congr (IsColimit.equivOfNatIsoOfIso
    (Functor.isoWhiskerLeft _ J.uliftYonedaIsoCompPresheafToSheaf.symm) _ _
    (Cocones.ext (Sheaf.isoMk (isoSheafify J ((isSheaf_iff_isSheaf_of_type _ _).2
      (Subcanonical.isSheaf_of_isRepresentable' _))).symm) (fun f => ?_)))
  ext
  simp only [id_obj, mapCocone_pt, Cocone.whisker_pt, Over.forgetCocone_pt, uliftYoneda_obj_val_obj,
    comp_obj, ObjectProperty.ι_obj, Over.forget_obj, isoWhiskerLeft_inv, Iso.symm_inv,
    Cocones.precompose_obj_pt, const_obj_obj, Cocones.precompose_obj_ι, NatTrans.comp_app,
    whiskerLeft_app, uliftYonedaIsoCompPresheafToSheaf_hom_app, sheafificationAdjunction_unit_app,
    mapCocone_ι_app, Cocone.whisker_ι, Over.forgetCocone_ι_app, Functor.comp_map, Sheaf.isoMk_hom,
    Iso.symm_hom, isoSheafify_inv, Category.assoc, Sheaf.comp_val,
    fullyFaithfulSheafToPresheaf_preimage_val, sheafifyMap_sheafifyLift, toSheafify_sheafifyLift,
    FunctorToTypes.comp, uliftYoneda_map_app, NatTrans.id_app, types_id_apply]
  rfl

theorem uliftYoneda_comp_presheafToSheaf :
    CategoryTheory.uliftYoneda.{u} ⋙ presheafToSheaf J (Type max u v) = J.uliftYoneda := by
  sorry

abbrev functorDiagram {X : C} (S : Sieve X) : S.arrows.category ⥤ Sheaf J (Type max u v) :=
  S.arrows.diagram ⋙ uliftYoneda.{u} J

lemma functorDiagram_eq_functorDiagram_comp_presheafToSheaf {X : C} (S : Sieve X) :
    J.functorDiagram S = S.functorDiagram ⋙ presheafToSheaf J (Type max u v) := by
  unfold functorDiagram Sieve.functorDiagram


noncomputable def desc {X : C} (S : Sieve X) :
    Limits.colimit (S.arrows.diagram ⋙ uliftYoneda.{u} J) ⟶ (uliftYoneda.{u} J).obj X :=
  Limits.colimit.desc _ (J.uliftYoneda.mapCocone S.arrows.cocone)

noncomputable def pullbackCone {X Y : C} (S : Sieve X) (f : Y ⟶ X) :
    Limits.PullbackCone ((uliftYoneda.{u} J).map f) (J.desc S) := by
  refine Limits.PullbackCone.mk (J.desc (S.pullback f))
    (Limits.colimit.pre (S.arrows.diagram ⋙ uliftYoneda.{u} J) (S.pullbackFunctor f))
    (Limits.colimit.hom_ext fun g => ?_)
  have : Limits.colimit.ι ((Sieve.pullback f S).arrows.diagram ⋙ uliftYoneda.{u} J) g =
      Limits.colimit.ι (S.pullbackFunctor f ⋙ S.arrows.diagram ⋙ uliftYoneda.{u} J) g := by
    congr
  simp only [id_obj, Sieve.pullback_apply, comp_obj, ObjectProperty.ι_obj, Over.forget_obj, desc,
    Limits.colimit.ι_desc_assoc, mapCocone_pt, Limits.Cocone.whisker_pt, Over.forgetCocone_pt,
    mapCocone_ι_app, Limits.Cocone.whisker_ι, whiskerLeft_app, Over.forgetCocone_ι_app,
    Limits.colimit.pre_desc]
  simp [this]

theorem colimit_pullback_isPullback' {X Y : C} (S : Sieve X) (f : Y ⟶ X) :
   IsPullback (J.desc (S.pullback f))
      (Limits.colimit.pre (S.arrows.diagram ⋙ uliftYoneda.{u} J) (S.pullbackFunctor f))
      ((uliftYoneda.{u} J).map f) (J.desc S) := by
  sorry

def presheafToSheafFunctorIsoColimit {X : C} (S : Sieve X) :
    (presheafToSheaf J (Type max u v)).obj (S.functor ⋙ uliftFunctor.{u}) ≅
      Limits.colimit (S.arrows.diagram ⋙ uliftYoneda.{u} J) := by
  sorry

omit [HasWeakSheafify (Sheaf.canonicalTopology C) (Type (max u v))] in
/-- A sieve of `X` belongs to a subcanonical topology `J` if and only if `uliftYoneda X` is a
colimit of the diagram associated to `S` composed with the Yoneda embedding into
`Sheaf J (Type max u v)`. -/
theorem covering_iff_colimit_uliftYoneda {X : C} (S : Sieve X) :
    S ∈ J X ↔ Nonempty (Limits.IsColimit
      ((GrothendieckTopology.uliftYoneda.{u} J).mapCocone S.arrows.cocone)) := by
  constructor
  · exact fun hS => Nonempty.intro {
      desc s := J.uliftYonedaEquiv.invFun ((s.pt.cond.isSheafFor S hS).amalgamate
        (J.familyOfElementsPtVal' s) (J.familyOfElementsPtVal_compatible' s))
      fac s j := by
        simp only [id_obj, comp_obj, ObjectProperty.ι_obj, Over.forget_obj, mapCocone_pt,
          Limits.Cocone.whisker_pt, Over.forgetCocone_pt, const_obj_obj, mapCocone_ι_app,
          Limits.Cocone.whisker_ι, whiskerLeft_app, Over.forgetCocone_ι_app, Equiv.invFun_as_coe,
          uliftYonedaEquiv_symm_naturality_left, Presieve.IsSheafFor.valid_glue _ _ _ j.property,
          familyOfElementsPtVal', J.uliftYonedaEquiv.symm_apply_apply]
        rfl
      uniq s m hm := by
        have h := (s.pt.cond.isSheafFor S hS) (J.familyOfElementsPtVal' s)
          (J.familyOfElementsPtVal_compatible' s)
        refine J.uliftYonedaEquiv.eq_symm_apply.2 (h.unique ?_ ?_)
        · intro _ _ _
          rw [familyOfElementsPtVal', J.uliftYonedaEquiv_naturality m, ← hm]
          rfl
        · exact (s.pt.cond.isSheafFor S hS).isAmalgamation (familyOfElementsPtVal_compatible' J s)
      }
  · refine fun ⟨h⟩ => J.mem_of_isSheafFor_pullback _ _ (fun F Y f => ?_)
    have iso_bot := (J.isIso_presheafToSheaf_uliftFunctorInclusion_iff' S).2 (Nonempty.intro h)
    have iso_top := ((S.isPullback_uliftFunctorInclusion_pullback f).map
      (presheafToSheaf J _)).isIso_fst_of_isIso
    have h_pullback : Limits.IsColimit ((GrothendieckTopology.uliftYoneda.{u} J).mapCocone
        (S.pullback f).arrows.cocone) := by
      refine IsColimit.equivOfNatIsoOfIso
        (isoWhiskerLeft _ (J.uliftYonedaIsoCompPresheafToSheaf.symm)) _ _ ?_
        ((isColimitOfPreserves (presheafToSheaf J _)
          (S.pullback f).isColimitFunctorCocone).extendIso
          ((presheafToSheaf J (Type (max u v))).map
          (Sieve.pullback f S).uliftFunctorInclusion))
      exact Cocones.ext (J.uliftYonedaIsoCompPresheafToSheaf.app _).symm
        (fun f => by ext; simp; rfl)
    refine fun x hx => ?_
    use J.uliftYonedaEquiv
      (h_pullback.desc (J.compatibleUliftYonedaFamily_toCocone F (S.pullback f).arrows x hx))
    constructor
    · intro _ g hg
      rw [J.uliftYonedaEquiv_naturality]
      have : J.uliftYoneda.map g =
          (J.uliftYoneda.mapCocone (S.pullback f).arrows.cocone).ι.app ⟨Over.mk g, hg⟩ := rfl
      rw [this, h_pullback.fac]
      simp
    · intro a ha
      rw [← h_pullback.uniq _ (J.uliftYonedaEquiv.invFun a)
        fun ⟨_, hf⟩ => by simp [uliftYonedaEquiv_symm_naturality_left, ha _ hf]]
      exact J.uliftYonedaEquiv.symm_apply_eq.1 rfl

open Limits Opposite

lemma hfjezkl {F : Sheaf J (Type max u v)} (S : Sieve F)
    (h : Nonempty (IsColimit S.arrows.cocone)) :
    S ∈ Sheaf.canonicalTopology (Sheaf J (Type max u v)) F := by
  --have := S.forallYonedaIsSheaf_iff_colimit.2 h
  exact (Sheaf.mem_grothendieckTopology_iff_colimit S).mpr h -- ?????? => not proven

theorem isColimitGenerate {X : C} (S : Presieve X) :
    Nonempty (IsColimit (J.yoneda.mapCocone (Sieve.generate S).arrows.cocone)) ↔
      Nonempty (IsColimit (J.yoneda.mapCocone S.cocone)) := by
  sorry
  -- use a lemma in mathlib : cofinal colimit iso ?

inductive overYonedaArrows (F : Cᵒᵖ ⥤ Type max u v) :
    (G : Cᵒᵖ ⥤ Type max u v) → (G ⟶ colimit (overYoneda'.{u, v, max u v} F)) → Prop where
  | of (Y : C) (s : F.obj (op Y)) : overYonedaArrows F (CategoryTheory.uliftYoneda.obj Y)
      (colimit.ι (overYoneda'.{u, v, max u v} F) ⟨op Y, s⟩)

theorem fnejzi (F : Sheaf (Sheaf.canonicalTopology (Sheaf J C)) (Type max u v)) :
      IsRepresentable F.val := by
    -- have e := natIsoColimitOverYoneda'.{u, v, max u v} F.val
    let S : Presieve (colimit (overYoneda'.{u, v, max u v} F.val)) :=
      fun Y => { f | overYonedaArrows F.val Y f }

    have : (colimit (overYoneda'.{u, v, max u v} F.val)).IsRepresentable := by
      sorry
      -- suffices Nonempty (Limits.IsColimit ()) by
      --  sorry
    exact isRepresentable_of_natIso' (Limits.colimit (overYoneda'.{u, v, max u v} F.val)) e.symm

/- section

open Limits

variable (F : Sheaf J (Type max u v))

def homEquivOverCompSections (G : Sheaf J (Type max u v)) :
    (F ⟶ G) ≃ (sectionOver.over F.val ⋙ G.val).sections where
  toFun α := ⟨
      fun s => α.val.app s.fst s.snd,
      fun {s s'} f => by
        change (α.val.app s.fst ≫ G.val.map f.fst) s.snd = α.val.app s'.fst s'.snd
        rw [← α.val.naturality]
        simp
    ⟩
  invFun σ := Sheaf.Hom.mk {
      app X x := σ.val (⟨X, x⟩ : sectionOver F.val),
      naturality {X Y} f := by
        ext x
        simp only [types_comp_apply,
          ← σ.prop ({ fst := f } : sectionOverMorphism F.val ⟨X, x⟩ ⟨Y, F.val.map f x⟩)]
        rfl
    }
  left_inv _ := rfl
  right_inv _ := rfl

def coyonedaObjIso :
    coyoneda.obj (Opposite.op F) ≅
      sheafToPresheaf J (Type max u v) ⋙ coyoneda.obj (Opposite.op F.val) :=
  NatIso.ofComponents (fun _ => (fullyFaithfulSheafToPresheaf J (Type max u v)).homEquiv.toIso)

noncomputable def coyonedaOpNatIsoWhiskeringLeftOverCompLim :
    coyoneda.obj (Opposite.op F) ≅
      sheafToPresheaf J _ ⋙ (whiskeringLeftOver F.val) ⋙ lim :=
  (coyonedaObjIso J F) ≪≫ isoWhiskerLeft _ (coyonedaOpNatIsoWhiskeringLeftOverCompLim' F.val)

def uliftFunctorIsoId : uliftFunctor.{u, max u v} ≅ .id (Type max u v) :=
  NatIso.ofComponents (fun X => Equiv.ulift.toIso)

@[simps]
def overYoneda : (sectionOver F.val)ᵒᵖ ⥤ (Sheaf J (Type max u v)) where
  obj s := J.uliftYoneda.obj s.unop.fst.unop
  map f := J.uliftYoneda.map f.unop.fst.unop

def overCompYonedaCompCoyonedaFlipNatIsoWhiskeringLeftOver :
    (sectionOver.over F.val ⋙ J.uliftYoneda.op ⋙ coyoneda).flip
      ≅ sheafToPresheaf J _ ⋙ (whiskeringLeftOver F.val) :=
  (flipFunctor _ _ _).mapIso (isoWhiskerLeft (sectionOver.over F.val)
    (J.largeCurriedUliftYonedaLemma ≪≫ isoWhiskerLeft (evaluation _ _)
      (isoWhiskerRight ((whiskeringRight _ _ _).mapIso uliftFunctorIsoId)
        ((whiskeringLeft _ _ _).obj _) ≪≫ (Iso.refl _))))

#check J.overYoneda F

instance : HasColimitsOfSize (Sheaf J (Type max u v)) :=
  Sheaf.instHasColimitsOfSize

noncomputable def coyonedaOpColimitOverYonedaNatIsoWhiskeringLeftOverLim :
    coyoneda.obj (Opposite.op (colimit (J.overYoneda F))) ≅
      sheafToPresheaf J _ ⋙ (whiskeringLeftOver F) ⋙ lim :=
  (coyonedaOpColimitIsoLimitCoyoneda' (overYoneda F)).trans
    ((limitIsoFlipCompLim _).trans
    (isoWhiskerRight (J.overCompYonedaCompCoyonedaFlipNatIsoWhiskeringLeftOver F) _))

theorem fnejzi (F : Sheaf (Sheaf.canonicalTopology C) (Type max u v)) : IsRepresentable F.val := by
    #check natIsoColimitOverYoneda'.{u, v, max u v} F.val
    sorry

end -/

end CategoryTheory.GrothendieckTopology
