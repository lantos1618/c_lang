FROM mcr.microsoft.com/devcontainers/rust:latest

# Install additional packages
RUN apt-get update && export DEBIAN_FRONTEND=noninteractive \
    && apt-get -y install --no-install-recommends \
        clang \
        lldb \
        lld \
    && apt-get clean -y \
    && rm -rf /var/lib/apt/lists/*

# Install additional Rust components
RUN rustup component add \
    rustfmt \
    clippy \
    rust-analysis \
    rust-src \
    rls 