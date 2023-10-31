# Fully faithful functors between precategories

```agda
module category-theory.fully-faithful-functors-precategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.faithful-functors-precategories
open import category-theory.full-functors-precategories
open import category-theory.fully-faithful-maps-precategories
open import category-theory.functors-precategories
open import category-theory.precategories

open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.propositions
open import foundation.surjective-maps
open import foundation.universe-levels
```

</details>

## Idea

A [functor](category-theory.functors-precategories.md) between
[precategories](category-theory.precategories.md) `C` and `D` is **fully
faithful** if it's an [equivalence](foundation-core.equivalences.md) on
hom-[sets](foundation-core.sets.md), or equivalently, a
[full](category-theory.full-functors-precategories.md) and
[faithful](category-theory.faithful-functors-precategories.md) functor on
precategories.

## Definitions

### The predicate of being fully faithful on functors between precategories

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2)
  (D : Precategory l3 l4)
  (F : functor-Precategory C D)
  where

  is-fully-faithful-functor-Precategory : UU (l1 ⊔ l2 ⊔ l4)
  is-fully-faithful-functor-Precategory =
    is-fully-faithful-map-Precategory C D (map-functor-Precategory C D F)

  is-prop-is-fully-faithful-functor-Precategory :
    is-prop is-fully-faithful-functor-Precategory
  is-prop-is-fully-faithful-functor-Precategory =
    is-prop-is-fully-faithful-map-Precategory C D
      ( map-functor-Precategory C D F)

  is-fully-faithful-prop-functor-Precategory : Prop (l1 ⊔ l2 ⊔ l4)
  is-fully-faithful-prop-functor-Precategory =
    is-fully-faithful-prop-map-Precategory C D
      ( map-functor-Precategory C D F)

  equiv-hom-is-fully-faithful-functor-Precategory :
    is-fully-faithful-functor-Precategory → {x y : obj-Precategory C} →
    hom-Precategory C x y ≃
    hom-Precategory D
      ( obj-functor-Precategory C D F x)
      ( obj-functor-Precategory C D F y)
  equiv-hom-is-fully-faithful-functor-Precategory =
    equiv-hom-is-fully-faithful-map-Precategory C D
      ( map-functor-Precategory C D F)

  inv-equiv-hom-is-fully-faithful-functor-Precategory :
    is-fully-faithful-functor-Precategory →
    {x y : obj-Precategory C} →
    hom-Precategory D
      ( obj-functor-Precategory C D F x)
      ( obj-functor-Precategory C D F y) ≃
    hom-Precategory C x y
  inv-equiv-hom-is-fully-faithful-functor-Precategory is-ff-F =
    inv-equiv (equiv-hom-is-fully-faithful-functor-Precategory is-ff-F)

  map-inv-hom-is-fully-faithful-functor-Precategory :
    is-fully-faithful-functor-Precategory →
    {x y : obj-Precategory C} →
    hom-Precategory D
      ( obj-functor-Precategory C D F x)
      ( obj-functor-Precategory C D F y) →
    hom-Precategory C x y
  map-inv-hom-is-fully-faithful-functor-Precategory is-ff-F =
    map-equiv (inv-equiv-hom-is-fully-faithful-functor-Precategory is-ff-F)
```

### The type of fully faithful functors between two precategories

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2)
  (D : Precategory l3 l4)
  where

  fully-faithful-functor-Precategory : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  fully-faithful-functor-Precategory =
    Σ (functor-Precategory C D) (is-fully-faithful-functor-Precategory C D)

  functor-fully-faithful-functor-Precategory :
    fully-faithful-functor-Precategory → functor-Precategory C D
  functor-fully-faithful-functor-Precategory = pr1

  is-fully-faithful-fully-faithful-functor-Precategory :
    (F : fully-faithful-functor-Precategory) →
    is-fully-faithful-functor-Precategory C D
      ( functor-fully-faithful-functor-Precategory F)
  is-fully-faithful-fully-faithful-functor-Precategory = pr2

  obj-fully-faithful-functor-Precategory :
    fully-faithful-functor-Precategory → obj-Precategory C → obj-Precategory D
  obj-fully-faithful-functor-Precategory =
    obj-functor-Precategory C D ∘ functor-fully-faithful-functor-Precategory

  hom-fully-faithful-functor-Precategory :
    (F : fully-faithful-functor-Precategory)
    {x y : obj-Precategory C} →
    hom-Precategory C x y →
    hom-Precategory D
      ( obj-fully-faithful-functor-Precategory F x)
      ( obj-fully-faithful-functor-Precategory F y)
  hom-fully-faithful-functor-Precategory =
    hom-functor-Precategory C D ∘ functor-fully-faithful-functor-Precategory

  equiv-hom-fully-faithful-functor-Precategory :
    (F : fully-faithful-functor-Precategory)
    {x y : obj-Precategory C} →
    hom-Precategory C x y ≃
    hom-Precategory D
      ( obj-fully-faithful-functor-Precategory F x)
      ( obj-fully-faithful-functor-Precategory F y)
  equiv-hom-fully-faithful-functor-Precategory F =
    equiv-hom-is-fully-faithful-functor-Precategory C D
      ( functor-fully-faithful-functor-Precategory F)
      ( is-fully-faithful-fully-faithful-functor-Precategory F)

  inv-equiv-hom-fully-faithful-functor-Precategory :
    (F : fully-faithful-functor-Precategory)
    {x y : obj-Precategory C} →
    hom-Precategory D
      ( obj-fully-faithful-functor-Precategory F x)
      ( obj-fully-faithful-functor-Precategory F y) ≃
    hom-Precategory C x y
  inv-equiv-hom-fully-faithful-functor-Precategory F =
    inv-equiv (equiv-hom-fully-faithful-functor-Precategory F)

  map-inv-hom-fully-faithful-functor-Precategory :
    (F : fully-faithful-functor-Precategory)
    {x y : obj-Precategory C} →
    hom-Precategory D
      ( obj-fully-faithful-functor-Precategory F x)
      ( obj-fully-faithful-functor-Precategory F y) →
    hom-Precategory C x y
  map-inv-hom-fully-faithful-functor-Precategory F =
    map-equiv (inv-equiv-hom-fully-faithful-functor-Precategory F)
```

## Properties

### Fully faithful functors are the same as full and faithful functors

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2)
  (D : Precategory l3 l4)
  (F : functor-Precategory C D)
  where

  is-full-is-fully-faithful-functor-Precategory :
    is-fully-faithful-functor-Precategory C D F →
    is-full-functor-Precategory C D F
  is-full-is-fully-faithful-functor-Precategory is-ff-F x y =
    is-surjective-is-equiv (is-ff-F x y)

  full-functor-is-fully-faithful-functor-Precategory :
    is-fully-faithful-functor-Precategory C D F → full-functor-Precategory C D
  pr1 (full-functor-is-fully-faithful-functor-Precategory is-ff-F) = F
  pr2 (full-functor-is-fully-faithful-functor-Precategory is-ff-F) =
    is-full-is-fully-faithful-functor-Precategory is-ff-F

  is-faithful-is-fully-faithful-functor-Precategory :
    is-fully-faithful-functor-Precategory C D F →
    is-faithful-functor-Precategory C D F
  is-faithful-is-fully-faithful-functor-Precategory is-ff-F x y =
    is-emb-is-equiv (is-ff-F x y)

  faithful-functor-is-fully-faithful-functor-Precategory :
    is-fully-faithful-functor-Precategory C D F →
    faithful-functor-Precategory C D
  pr1 (faithful-functor-is-fully-faithful-functor-Precategory is-ff-F) = F
  pr2 (faithful-functor-is-fully-faithful-functor-Precategory is-ff-F) =
    is-faithful-is-fully-faithful-functor-Precategory is-ff-F

  is-fully-faithful-is-full-is-faithful-functor-Precategory :
    is-full-functor-Precategory C D F →
    is-faithful-functor-Precategory C D F →
    is-fully-faithful-functor-Precategory C D F
  is-fully-faithful-is-full-is-faithful-functor-Precategory
    is-full-F is-faithful-F x y =
    is-equiv-is-emb-is-surjective (is-full-F x y) (is-faithful-F x y)

  fully-faithful-functor-is-full-is-faithful-functor-Precategory :
    is-full-functor-Precategory C D F →
    is-faithful-functor-Precategory C D F →
    fully-faithful-functor-Precategory C D
  pr1
    ( fully-faithful-functor-is-full-is-faithful-functor-Precategory
      is-full-F is-faithful-F) =
    F
  pr2
    ( fully-faithful-functor-is-full-is-faithful-functor-Precategory
      is-full-F is-faithful-F) =
    is-fully-faithful-is-full-is-faithful-functor-Precategory
      ( is-full-F) (is-faithful-F)

module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2)
  (D : Precategory l3 l4)
  (F : fully-faithful-functor-Precategory C D)
  where

  full-functor-fully-faithful-functor-Precategory : full-functor-Precategory C D
  full-functor-fully-faithful-functor-Precategory =
    full-functor-is-fully-faithful-functor-Precategory C D
      ( functor-fully-faithful-functor-Precategory C D F)
      ( is-fully-faithful-fully-faithful-functor-Precategory C D F)

  faithful-functor-fully-faithful-functor-Precategory :
    faithful-functor-Precategory C D
  faithful-functor-fully-faithful-functor-Precategory =
    faithful-functor-is-fully-faithful-functor-Precategory C D
      ( functor-fully-faithful-functor-Precategory C D F)
      ( is-fully-faithful-fully-faithful-functor-Precategory C D F)
```

### Fully faithful functors reflect isomorphisms

This remains to be formalized.