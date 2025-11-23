#!/usr/bin/env uv run
from livereload import Server, shell
server = Server()
server.watch('src/**/*.md', shell('make'))
server.serve(root='html', port=5321)
