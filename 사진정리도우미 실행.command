#!/bin/bash
# 사진 정리 도우미 실행 파일: 더블클릭하면 브라우저에 검토 화면이 열립니다.
cd "$(dirname "$0")"
if ! command -v python3 >/dev/null 2>&1; then
  echo "python3가 없습니다. 터미널에서 xcode-select --install 을 실행해 설치한 뒤 다시 실행하세요."
  read -r -p "엔터를 누르면 창이 닫힙니다."
  exit 1
fi
python3 photo_review.py
