# Jech Library Setup

## Requirements
- Coq 8.13 or later
- Docker (for CI)

## Local Compilation
To compile the `Jech.v` file locally, you can use the following command:
```bash
coqc -Q . '' Jech.v
```

## CI Setup
The `.gitlab-ci.yml` file is configured to run in GitLab CI using the `coqorg/coq` Docker image. To use this setup, you need to have GitLab CI configured in your project.
