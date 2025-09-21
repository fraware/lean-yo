# Multi-stage build for LeanYo library
FROM leanprover/lean4:v4.8.0 as builder

# Set working directory
WORKDIR /app

# Copy project files
COPY lean-toolchain ./
COPY lakefile.lean ./
COPY lake-manifest.json ./
COPY LeanYo.lean ./
COPY LeanYo/ ./LeanYo/

# Update lake dependencies and build
RUN lake update && lake build

# Create final runtime image
FROM leanprover/lean4:v4.8.0

# Install additional tools
RUN apt-get update && apt-get install -y \
    python3 \
    python3-pip \
    git \
    && rm -rf /var/lib/apt/lists/*

# Set working directory
WORKDIR /app

# Copy built artifacts from builder stage
COPY --from=builder /app/.lake ./.lake
COPY --from=builder /app/lake-packages ./lake-packages
COPY --from=builder /app/LeanYo ./LeanYo
COPY --from=builder /app/LeanYo.lean ./
COPY --from=builder /app/lakefile.lean ./
COPY --from=builder /app/lake-manifest.json ./
COPY --from=builder /app/lean-toolchain ./

# Copy additional files
COPY README.md ./
COPY LICENSE ./
COPY docs/ ./docs/
COPY scripts/ ./scripts/

# Create a lean-yo command script
RUN echo '#!/bin/bash\n\
    if [ "$1" = "--help" ] || [ "$1" = "-h" ] || [ $# -eq 0 ]; then\n\
    echo "LeanYo - A Lean 4 tactic library for category theory"\n\
    echo ""\n\
    echo "Usage:"\n\
    echo "  lean-yo --help                 Show this help message"\n\
    echo "  lean-yo --version              Show version information"\n\
    echo "  lean-yo --examples             Run example proofs"\n\
    echo "  lean-yo --test                 Run test suite"\n\
    echo "  lean-yo --validate             Validate lemma database"\n\
    echo "  lean-yo <file.lean>            Process a Lean file with LeanYo"\n\
    echo ""\n\
    echo "Interactive usage:"\n\
    echo "  docker run -it --rm -v $(pwd):/workspace ghcr.io/fraware/lean-yo:latest bash"\n\
    echo ""\n\
    echo "Examples:"\n\
    echo "  # Run examples"\n\
    echo "  docker run --rm ghcr.io/fraware/lean-yo:latest --examples"\n\
    echo ""\n\
    echo "  # Process your own file"\n\
    echo "  docker run --rm -v $(pwd):/workspace ghcr.io/fraware/lean-yo:latest /workspace/my_proof.lean"\n\
    echo ""\n\
    echo "Documentation: https://github.com/fraware/lean-yo/tree/main/docs"\n\
    exit 0\n\
    fi\n\
    \n\
    case "$1" in\n\
    --version)\n\
    echo "LeanYo version: $(cat lean-toolchain | cut -d: -f2)"\n\
    echo "Lean version: $(lean --version)"\n\
    ;;\n\
    --examples)\n\
    echo "Running LeanYo examples..."\n\
    if [ -f "LeanYo/Examples.lean" ]; then\n\
    lake exe lean LeanYo/Examples.lean\n\
    else\n\
    echo "Examples file not found. Building and testing library instead..."\n\
    lake build\n\
    fi\n\
    ;;\n\
    --test)\n\
    echo "Running LeanYo test suite..."\n\
    lake build\n\
    if [ -f "scripts/production_test.py" ]; then\n\
    python3 scripts/production_test.py\n\
    fi\n\
    ;;\n\
    --validate)\n\
    echo "Validating LeanYo lemma database..."\n\
    if [ -f "scripts/validate_lemmas.py" ]; then\n\
    python3 scripts/validate_lemmas.py\n\
    else\n\
    echo "Validation script not found"\n\
    exit 1\n\
    fi\n\
    ;;\n\
    *.lean)\n\
    echo "Processing Lean file: $1"\n\
    lake exe lean "$1"\n\
    ;;\n\
    *)\n\
    echo "Unknown option: $1"\n\
    echo "Run lean-yo --help for usage information"\n\
    exit 1\n\
    ;;\n\
    esac' > /usr/local/bin/lean-yo && chmod +x /usr/local/bin/lean-yo

# Set default command
ENTRYPOINT ["/usr/local/bin/lean-yo"]
CMD ["--help"]

# Labels for metadata
LABEL org.opencontainers.image.title="LeanYo"
LABEL org.opencontainers.image.description="A Lean 4 tactic library that simplifies category theory proofs using (co)Yoneda isomorphisms"
LABEL org.opencontainers.image.url="https://github.com/fraware/lean-yo"
LABEL org.opencontainers.image.documentation="https://github.com/fraware/lean-yo/tree/main/docs"
LABEL org.opencontainers.image.source="https://github.com/fraware/lean-yo"
LABEL org.opencontainers.image.licenses="MIT"
