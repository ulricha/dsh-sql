#!/bin/bash

cabal sandbox delete
cabal sandbox init

cabal sandbox add-source $HOME/work/dev/hdbc-postgresql
cabal sandbox add-source $HOME/work/dev/algebra-dag
cabal sandbox add-source $HOME/work/dev/algebra-sql
cabal sandbox add-source $HOME/work/dev/dsh
cabal install --dependencies-only
cabal configure

