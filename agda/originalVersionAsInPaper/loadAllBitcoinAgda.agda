module loadAllBitcoinAgda where

-- this file loads the files containing the code examples in the
-- paper Anton Setzer: Modelling Bitcopins in Agda

-- Sect 1 introduction
-- Sect 2 Introduction to Agda

import agdaIntro.finn
import agdaIntro.Equality
import agdaIntro.student

-- Sect 3 A Basic Ledger Based Model of Bitcoins
-- Sect 4 Bitcoin Ledger in Agda

import bitcoinLedgerModel
import libraries.listLib

-- Sect 5 From a Ledger to a Transaction Tree
-- Sect 6 Transaction Trees in Agda

import bitcoinTreeModel
import libraries.listLib

-- Sect 7 Correctness and Limitations of the Model
-- Sect 8 Conclusion
