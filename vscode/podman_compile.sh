set -e
podman build . -t moorhenvscode
container_id=$(podman create localhost/moorhenvscode)
podman cp "$container_id:/moorhenvscode/moorhen-highlighting-0.1.0.vsix" .
podman rm "$container_id"
