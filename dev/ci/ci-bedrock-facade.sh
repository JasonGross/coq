#!/usr/bin/env bash

ci_dir="$(dirname "$0")"
source ${ci_dir}/ci-common.sh

bedrock_facade_CI_DIR=${CI_BUILD_DIR}/bedrock-facade

git_checkout --recursive ${bedrock_facade_CI_BRANCH} ${bedrock_facade_CI_GITURL} ${bedrock_facade_CI_DIR}

( cd ${bedrock_facade_CI_DIR} && ./etc/coq-scripts/timing/make-pretty-timed.sh -j ${NJOBS} facade && make -j ${NJOBS} facade )
