FROM python:3.12-slim

WORKDIR /app
COPY cloud_mahjong_server.py /app/cloud_mahjong_server.py

ENV PORT=8000
EXPOSE 8000

CMD ["sh", "-c", "python cloud_mahjong_server.py --host 0.0.0.0 --port ${PORT}"]
