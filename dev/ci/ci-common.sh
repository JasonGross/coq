#!/usr/bin/env bash

set -xe

# default value for NJOBS
: "${NJOBS:=1}"
export NJOBS

# We add $PWD/_install_ci/lib unconditionally due to a hack in the
# ci-menhir script, which will install some OCaml libraries outside
# our docker-opam / Nix setup; we have to do this for all the 3 cases
# below; would we fix ci-menhir, then we just do this for the first
# branch [ci case]
if which cygpath >/dev/null 2>&1; then OCAMLFINDSEP=\;; else OCAMLFINDSEP=:; fi
export OCAMLPATH="$PWD/_install_ci/lib$OCAMLFINDSEP$OCAMLPATH"
export PATH="$PWD/_install_ci/bin:$PATH"

# We can remove setting COQLIB and COQCORELIB from here, but better to
# wait until we have merged the coq.boot patch so we can do this in a
# more controlled way.
if [ -n "${GITLAB_CI}" ];
then
    # Gitlab build, Coq installed into `_install_ci`
    export COQBIN="$PWD/_install_ci/bin"
    export CI_BRANCH="$CI_COMMIT_REF_NAME"
    if [[ ${CI_BRANCH#pr-} =~ ^[0-9]*$ ]]
    then
        export CI_PULL_REQUEST="${CI_BRANCH#pr-}"
    fi
elif [ -d "$PWD/_build/install/default/" ];
then
    # Full Dune build, we basically do what `dune exec --` does
    export OCAMLPATH="$PWD/_build/install/default/lib/$OCAMLFINDSEP$OCAMLPATH"
    export COQBIN="$PWD/_build/install/default/bin"
    export COQLIB="$PWD/_build/install/default/lib/coq"
    export COQCORELIB="$PWD/_build/install/default/lib/coq-core"
    CI_BRANCH="$(git rev-parse --abbrev-ref HEAD)"
    export CI_BRANCH
fi

export PATH="$COQBIN:$PATH"

# Coq's tools need an ending slash :S, we should fix them.
export COQBIN="$COQBIN/"

ls -l "$COQBIN"

# Where we download and build external developments
CI_BUILD_DIR="$PWD/_build_ci"

# Where we install external binaries and ocaml libraries
CI_INSTALL_DIR="$PWD/_install_ci"

ls -l "$CI_BUILD_DIR" || true

declare -A overlays

# overlay <project> <giturl> <ref> <prnumber> [<prbranch>]
#   creates an overlay for project using a given url and branch which is
#   active for prnumber or prbranch. prbranch defaults to ref.
function overlay()
{
    local project=$1
    local ov_url=$2
    local ov_ref=$3
    local ov_prnumber=$4
    local ov_prbranch=$5
    : "${ov_prbranch:=$ov_ref}"

    if [ "$CI_PULL_REQUEST" = "$ov_prnumber" ] || [ "$CI_BRANCH" = "$ov_prbranch" ]; then
      if ! is_in_projects "$project"; then
        echo "Error: $1 is not a known project which can be overlayed"
        exit 1
      fi

      overlays[${project}_URL]=$ov_url
      overlays[${project}_REF]=$ov_ref
    fi
}

set +x
# shellcheck source=ci-basic-overlay.sh
. "${ci_dir}/ci-basic-overlay.sh"

for overlay in "${ci_dir}"/user-overlays/*.sh; do
    # shellcheck source=/dev/null
    # the directoy can be empty
    if [ -e "${overlay}" ]; then . "${overlay}"; fi
done
set -x

# [git_download project] will download [project] and unpack it
# in [$CI_BUILD_DIR/project] if the folder does not exist already;
# if it does, it will do nothing except print a warning (this can be
# useful when building locally).
# Note: when there is an overlay, $WITH_SUBMODULES is set to 1 or $CI is unset or empty
# (local build), it uses git clone to perform the download.
git_download()
{
  local project=$1
  local project_dest="$CI_BUILD_DIR/$project"
  local dest="$project_dest" # will be changed later if we're in a submodule

  local giturl_var="${project}_CI_GITURL"
  local giturl="${!giturl_var}"
  local ref_var="${project}_CI_REF"
  local ref="${!ref_var}"
  local ref_for_rebase="$ref" # might be distinct from $ref if we're in a submoudle
  local parent_project_var="${project}_CI_PARENT_PROJECT"
  local parent_project="${!parent_project_var}"
  local submodule_folder_var="${project}_CI_SUBMODULE_FOLDER"
  local submodule_folder="${!submodule_folder_var}"

  local ov_url=${overlays[${project}_URL]}
  local ov_ref=${overlays[${project}_REF]}

  local in_subfolder=""

  # if there is a parent project, we first download the parent project
  # then symlink the submodule_folder to dest; this allows project CI scripts
  # to be transparent w.r.t. whether or not the project is cloned from
  # a submodule / submodule_folder.
  # we can't symlink until the folder exists though.
  if [[ -n "${parent_project}" ]]; then
    WITH_SUBMODULES=1 git_download "${parent_project}"

    # if the parent project still has its .git directory, we can reuse
    # it (this is not the case, for example, when it comes from a
    # downloaded CI artifact)
    if [[ -d "${CI_BUILD_DIR}/${parent_project}/.git" ]]; then
      local dest="${parent_project}"
    else
      # otherwise we must re-download the parent project
      local dest="${project_dest}-PARENT"
    fi
  fi

  if [ -d "$project_dest" ]; then
    echo "Warning: download and unpacking of $project skipped because $project_dest already exists."
  elif [[ $ov_url ]] || [ "$WITH_SUBMODULES" = "1" ] || [ "$CI" = "" ] || [[ -n "${parent_project}" ]]; then
    if [ ! -d "$dest" ]; then
      echo "Notice: download and unpacking of $parent_project skipped because $dest already exists."
      pushd "$dest"
    else
      git clone "$giturl" "$dest"
      pushd "$dest"
      git checkout "$ref"
    fi
    git log -n 1
    if [[ $ov_url ]]; then
        # In CI we merge into the upstream branch to stay synchronized
        # Locally checkout the overlay and rebase on upstream
        # We act differently because merging is what will happen when the PR is merged
        # but rebasing produces something that is nicer to edit
        #
        # We must cd into the submodule_folder first, though, to
        # ensure that if it is a submodule we merge in the right way
        if [[ -n "$submodule_folder" ]]; then
          if [ "$WITH_SUBMODULES" = 1 ]; then
            git submodule update --init --recursive
          fi
          pushd "$submodule_folder"
          in_submodule_folder=1
          ref_for_rebase="$(git rev-parse HEAD)"
        fi
        if [[ $CI ]]; then
            git -c pull.rebase=false -c user.email=nobody@example.invalid -c user.name=Nobody \
                pull --no-edit --no-ff "$ov_url" "$ov_ref"
            git log -n 1 HEAD^2 || true # no merge commit if the overlay was merged upstream
            git log -n 1
        else
            git remote add -t "$ov_ref" -f overlay "$ov_url"
            git checkout -b "$ov_ref" overlay/"$ov_ref"
            git rebase "$ref_for_rebase"
            git log -n 1
        fi
    fi
    if [ "$WITH_SUBMODULES" = 1 ]; then
        git submodule update --init --recursive
    fi
    if [ "$in_submodule_folder" = 1 ]; then
        popd
    fi
    popd
  else # When possible, we download tarballs to reduce bandwidth and latency
    local archiveurl_var="${project}_CI_ARCHIVEURL"
    local archiveurl="${!archiveurl_var}"
    mkdir -p "$dest"
    pushd "$dest"
    local commit
    commit=$(git ls-remote "$giturl" "refs/heads/$ref" | cut -f 1)
    if [[ "$commit" == "" ]]; then
      # $ref must have been a tag or hash, not a branch
      commit="$ref"
    fi
    wget "$archiveurl/$commit.tar.gz"
    tar xfz "$commit.tar.gz" --strip-components=1
    rm -f "$commit.tar.gz"
    popd
  fi

  # now we can create the symlinks
  if [[ -n "$submodule_folder" ]]; then
    if [ -e "$project_dest" ]; then
      echo "Warning: symlinking of $dest/$submodule_folder for $project skipped because $project_dest already exists"
    else
      ln -s "$dest/$submodule_folder" "$project_dest"
    fi
  fi
}

make()
{
    # +x: add x only if defined
    if [ -z "${MAKEFLAGS+x}" ] && [ -n "${NJOBS}" ];
    then
        # Not submake and parallel make requested
        command make -j "$NJOBS" "$@"
    else
        command make "$@"
    fi
}

# run make -k; make again if it failed so that the failing file comes last
# makes it easier to find the error messages in the CI log
function make_full() {
    if ! make -k "$@"; then make -k "$@"; exit 1; fi
}
