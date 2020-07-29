# Project -1 Implementation of 2PC protocol with BTM nad RM failures

- Implemented Two Phase Commit, 2PC, protocol with backup transaction manager, BTM in Pluscal.
- Tested the model by translating into TLA+ model on Temporal (Termination and Completed) and Invariant (Consistency) properties.
- 2PC protocol is a transaction management protocol for distributed set up which aims to achieve atomic transactions in distributed set up similar to atomic transactions in single database instances.
- In case o Transaction Manager failure Back-up Transaction Manager is used. It will take over the actions performed by TM and will make sure it aborts all the RM's.
- In case of Resouce Manager failure we will save the state of the system and will restart where it is when the RM is fixed.

                           

