#!/usr/bin/env python3
# Pseudoterminal wrapper script

import pty
from sys import argv

def main():
    if len(argv) < 2:
        print(f"Usage: {argv[0]} [command]")
        return
    pty.spawn(argv[1:])

if __name__ == "__main__":
    main()