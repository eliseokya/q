# A Categorical Model of Ethereum and Ethereum-Based Blockchains

---

## I. Base Category: Ethereum as a Transactional Category

**Category** $\mathcal{E}$ — the base category representing Ethereum

- **Objects** $\operatorname{Ob}(\mathcal{E})$: Accounts (Externally Owned Accounts \[EOAs] and Contract Accounts \[CAs])  
- **Morphisms** $\operatorname{Hom}_{\mathcal{E}}(A,B)$: Transactions or function calls from account $A$ to $B$  
- **Composition**: Sequential application of transactions, respecting Ethereum’s execution semantics  
- **Identity morphism**: A no-op transaction (null or idle action)  

---

## II. Smart Contracts as Internal Structures or Sub-Categories

A **Smart Contract** $C$ can be viewed as a sub-category $\mathcal{C}_C \subseteq \mathcal{E}$:

- Internally defines a set of callable functions (morphisms) $f_i : S_i \to S_j$  
- Contract state transitions are the internal morphisms of $\mathcal{C}_C$  

---

## III. Protocols as Functors

A **Protocol** $P$ is modelled as a functor:

$$F_P : \mathcal{E} \longrightarrow \mathcal{E}'$$

- Example: a bridge protocol acts as a functor from Ethereum to Arbitrum  
- Functoriality preserves identity and composition, ensuring state consistency, atomicity, and order of operations  

---

## IV. Execution as Diagrams

- Transactions and their internal calls form **diagrams** in $\mathcal{E}$  
- **Commutative diagrams** encode logical correctness (e.g., composed function-call chains resolve to deterministic states)  

---

## V. Finite-State Machines as Categories

Smart contracts can also be viewed as **finite-state machines (FSMs)**:

- **Objects**: Contract states  
- **Morphisms**: Transitions (guarded function calls)  
- The full execution logic corresponds to a state-transition diagram, i.e.
  a small category  

---

## VI. Monoidal Categories for Parallelism

To model parallel or batched execution:

- Introduce a **monoidal structure** $(\mathcal{E},\otimes,\mathbf{I})$  
- The tensor product $\otimes$ represents simultaneous transactions or batch operations  
- Useful for MEV analysis, batch swaps, and roll-up execution  

---

## VII. Higher Categories & Cross-Chain Logic

Cross-chain operations naturally inhabit a **2-category** or **bicategory**:

- **Objects**: Blockchains (Ethereum, Optimism, Arbitrum, …)  
- **1-Morphisms**: Protocol mappings (bridges, relayers)  
- **2-Morphisms**: Transformations between bridge logics (e.g., upgrades, dispute resolvers)  

---

## VIII. Limits & Colimits for Aggregation

- **Oracles**: Colimit over validator or data-provider inputs  
- **Flash-loan strategies**: Diagram whose optimal composition (colimit) yields maximum profit  
- **Roll-ups**: Limit of all L2 transaction batches resolving to an L1 state  

---

## Next Steps

1. Formalise the category $\mathcal{E}$ with explicit signatures and typing rules.  
2. Construct concrete examples — e.g.
   *Uniswap V2* as a functor, a flash-loan path as a commutative diagram.  
3. Explore *adjunctions* (e.g., **deposit** \(\dashv\) **withdraw**).  
4. Design and prototype a **categorical DSL** for specifying Ethereum protocols. 