## Key Definitions and Theorems

### Set Operations
- **Definition**: `my_set := {1, 2, 3}`
  - **Description**: Defines a set containing the elements 1, 2, and 3.
  - **Example**:
    ```coq
    Definition my_set := {1, 2, 3}.
    Compute in 1 my_set. (* Returns true *)
    Compute in 4 my_set. (* Returns false *)
    ```

### Membership Notation
- **Notation**: `x ∈ y`
  - **Description**: Checks if an element `x` is a member of set `y`.
  - **Example**:
    ```coq
    Notation "x ∈ y" := (tin x y) (at level 50).
    ```

### Singleton Set
- **Notation**: `{ x }``
  - **Description**: Creates a singleton set containing the element `x`.
  - **Example**:
    ```coq
    Notation "{ x }`" := (Sing x).
    ```

### Theorem Example
- **Theorem**: `t1 (x:Ens) : x ∈ { x }``
  - **Description**: Proves that an element `x` is a member of the singleton set `{ x }``.
  - **Proof**:
    ```coq
    Theorem t1 (x:Ens) : x ∈ { x }`.
    Proof.
      unfold tin, sIN.
      unfold Sing.
      unfold Paire.
      simpl.
      exists true.
      simpl.
      apply EQ_refl.
    Defined.
    ```

### Usage Instructions
1. **Import the Jech Library**:
   ```coq
   Require Import Jech.
   ```
2. **Define Sets**:
   ```coq
   Definition my_set := {1, 2, 3}.
   ```
3. **Check Membership**:
   ```coq
   Compute in 1 my_set.
   ```
4. **Prove Theorems**:
   ```coq
   Theorem t1 (x:Ens) : x ∈ { x }`.
   Proof.
     unfold tin, sIN.
     unfold Sing.
     unfold Paire.
     simpl.
     exists true.
     simpl.
     apply EQ_refl.
   Defined.
   ```
