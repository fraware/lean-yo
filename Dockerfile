# Multi-stage build for LeanYo library
FROM leanprover/lean4:v4.8.0 AS builder

WORKDIR /app

COPY lean-toolchain ./
COPY lakefile.lean ./
COPY lake-manifest.json ./
COPY LeanYo.lean ./
COPY LeanYo/ ./LeanYo/

RUN lake update && lake build

FROM leanprover/lean4:v4.8.0

RUN apt-get update && apt-get install -y --no-install-recommends \
    python3 \
    git \
    && rm -rf /var/lib/apt/lists/*

WORKDIR /app

COPY --from=builder /app/.lake ./.lake
COPY --from=builder /app/LeanYo ./LeanYo
COPY --from=builder /app/LeanYo.lean ./
COPY --from=builder /app/lakefile.lean ./
COPY --from=builder /app/lake-manifest.json ./
COPY --from=builder /app/lean-toolchain ./

COPY README.md ./
COPY LICENSE ./
COPY docs/ ./docs/
COPY scripts/ ./scripts/

RUN chmod +x scripts/docker-entrypoint.sh \
    && ln -sf /app/scripts/docker-entrypoint.sh /usr/local/bin/lean-yo

ENTRYPOINT ["/usr/local/bin/lean-yo"]
CMD ["--help"]

LABEL org.opencontainers.image.title="LeanYo"
LABEL org.opencontainers.image.description="A Lean 4 tactic library that simplifies category theory proofs using (co)Yoneda isomorphisms"
LABEL org.opencontainers.image.url="https://github.com/fraware/lean-yo"
LABEL org.opencontainers.image.documentation="https://github.com/fraware/lean-yo/tree/main/docs"
LABEL org.opencontainers.image.source="https://github.com/fraware/lean-yo"
LABEL org.opencontainers.image.licenses="MIT"
