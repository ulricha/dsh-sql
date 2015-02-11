#!/bin/bash

${PWD}/.cabal-sandbox/bin/vldot -i ${1}_vl.plan | dot -Tpdf -o ${1}_vl.pdf
${PWD}/.cabal-sandbox/bin/vldot -i ${1}_vl_opt.plan | dot -Tpdf -o ${1}_vl_opt.pdf
${PWD}/.cabal-sandbox/bin/tadot -i ${1}_ta.plan | dot -Tpdf -o ${1}_ta.pdf
${PWD}/.cabal-sandbox/bin/tadot -i ${1}_opt_ta.plan | dot -Tpdf -o ${1}_opt_ta.pdf
