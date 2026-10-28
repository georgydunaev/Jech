# Jech Library Installation Instructions

## Requirements
- Coq 8.13 or later
- Docker (optional, for CI and development)

## Local Installation

### Install Coq
To install Coq, you can use the following command:

```bash
sudo apt-get update && sudo apt-get install -y coq
```

### Clone the Jech Repository
To clone the Jech repository, you can use the following command:

```bash
git clone https://github.com/your-username/Jech.git
```

### Compile the Jech Library
To compile the `Jech.v` file, you can use the following command:

```bash
coqc -Q . '' Jech.v
```

## Docker Setup

### Build the Docker Image
To build the Docker image with the `coqorg/coq` image, you can use the following command:

```bash
docker build -t jech-coq .
```

### Run the Docker Container
To run the Docker container with the Jech library, you can use the following command:

```bash
docker run -it --rm -v $(pwd):/Jech jech-coq
```

## CI Setup

The `.gitlab-ci.yml` file is configured to run in GitLab CI using the `coqorg/coq` Docker image. To use this setup, you need to have GitLab CI configured in your project.
