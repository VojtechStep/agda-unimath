---
title: Univalent Mathematics in Agda
---

```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module foundation.contractible-maps where

open import foundation.coherently-invertible-maps using
  ( is-coherently-invertible; inv-is-coherently-invertible;
    issec-inv-is-coherently-invertible; isretr-inv-is-coherently-invertible;
    coh-inv-is-coherently-invertible)
open import foundation.contractible-types using (is-contr; center; contraction)
open import foundation.dependent-pair-types using (pair; pr1; pr2)
open import foundation.equivalences using
  ( is-equiv; is-equiv-has-inverse; is-coherently-invertible-is-equiv)
open import foundation.fibers-of-maps using (fib; eq-Eq-fib)
open import foundation.functions using (_∘_; id)
open import foundation.homotopies using (_~_; _·r_; _·l_)
open import foundation.identity-types using
  ( Id; ap; inv; _∙_; refl; right-unit)
open import foundation.universe-levels using (Level; UU; _⊔_)
```

# Contractible maps

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-contr-map : (A → B) → UU (l1 ⊔ l2)
  is-contr-map f = (y : B) → is-contr (fib f y)
```

## Any contractible map is an equivalence

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B}
  where
  
  map-inv-is-contr-map : is-contr-map f → B → A
  map-inv-is-contr-map H y = pr1 (center (H y))

  issec-map-inv-is-contr-map :
    (H : is-contr-map f) → (f ∘ (map-inv-is-contr-map H)) ~ id
  issec-map-inv-is-contr-map H y = pr2 (center (H y))

  isretr-map-inv-is-contr-map :
    (H : is-contr-map f) → ((map-inv-is-contr-map H) ∘ f) ~ id
  isretr-map-inv-is-contr-map H x =
    ap ( pr1 {B = λ z → Id (f z) (f x)})
       ( ( inv
           ( contraction
             ( H (f x))
             ( pair
               ( map-inv-is-contr-map H (f x))
               ( issec-map-inv-is-contr-map H (f x))))) ∙
         ( contraction (H (f x)) (pair x refl)))

  abstract
    is-equiv-is-contr-map : is-contr-map f → is-equiv f
    is-equiv-is-contr-map H =
      is-equiv-has-inverse
        ( map-inv-is-contr-map H)
        ( issec-map-inv-is-contr-map H)
        ( isretr-map-inv-is-contr-map H)
```

## Any coherently invertible map is a contractible map

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B}
  where

  abstract
    center-fib-is-coherently-invertible :
      is-coherently-invertible f → (y : B) → fib f y
    pr1 (center-fib-is-coherently-invertible H y) =
      inv-is-coherently-invertible H y
    pr2 (center-fib-is-coherently-invertible H y) =
      issec-inv-is-coherently-invertible H y

    contraction-fib-is-coherently-invertible :
      (H : is-coherently-invertible f) → (y : B) → (t : fib f y) →
      Id (center-fib-is-coherently-invertible H y) t
    contraction-fib-is-coherently-invertible H y (pair x refl) =
      eq-Eq-fib f y
        ( isretr-inv-is-coherently-invertible H x)
        ( ( right-unit) ∙
          ( inv ( coh-inv-is-coherently-invertible H x)))

  is-contr-map-is-coherently-invertible : 
    is-coherently-invertible f → is-contr-map f
  pr1 (is-contr-map-is-coherently-invertible H y) =
    center-fib-is-coherently-invertible H y
  pr2 (is-contr-map-is-coherently-invertible H y) =
    contraction-fib-is-coherently-invertible H y
```

## Any equivalence is a contractible map

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B}
  where
  
  abstract
    is-contr-map-is-equiv : is-equiv f → is-contr-map f
    is-contr-map-is-equiv =
      is-contr-map-is-coherently-invertible ∘ is-coherently-invertible-is-equiv
```