# Base image https://github.com/microsoft/vscode-dev-containers/tree/v0.194.3/containers/ubuntu/.devcontainer/base.Dockerfile

# Update the VARIANT to pick an Ubuntu version
ARG VARIANT="jammy"
FROM mcr.microsoft.com/vscode/devcontainers/base:0-${VARIANT}

# https://www.swi-prolog.org/build/PPA.html
RUN export DEBIAN_FRONTEND=noninteractive \
    && apt-get update \
    && apt-get install -y --no-install-recommends software-properties-common \
    && apt-add-repository ppa:swi-prolog/stable \
    && apt-get update \
    && apt-get install -y --no-install-recommends swi-prolog
