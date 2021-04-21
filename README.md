# CKB-verification
Verification of the [CKB block synchronization protocol](https://github.com/nervosnetwork/rfcs/blob/master/rfcs/0004-ckb-block-sync/0004-ckb-block-sync.md) using the Coq proof assistant.
### Requirement
Coq 8.8.1
### Building
Using `make all` to check the proofs.
### Contents
* `Blocks.v` - Some useful functions for the formalization.
* `Stage_1.v` - Modeling and verification of the first stage(connecting header stage).
* `Stage_2.v` - Modeling and verification of the second stage(downloading block stage).
* `Stage_3.v` - Modeling and verification of the third stage(accepting block stage).
* `Attack_simulation.v` - Attack simulation for the protocol.
