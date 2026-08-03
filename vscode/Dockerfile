FROM alpine:3.24

RUN apk update && apk add --no-cache nodejs npm

RUN npm install -g @vscode/vsce

WORKDIR /moorhenvscode
COPY . .
RUN vsce package --allow-missing-repository
